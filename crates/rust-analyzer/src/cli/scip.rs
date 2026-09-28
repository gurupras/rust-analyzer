//! SCIP generator

use std::{path::PathBuf, time::Instant};

use ide::{
    AnalysisHost, LineCol, Moniker, MonikerDescriptorKind, MonikerIdentifier, MonikerResult,
    PackageInformation, RootDatabase, StaticIndex, StaticIndexedFile, SymbolInformationKind,
    TextRange, TokenId, TokenStaticData, VendoredLibrariesConfig,
};
use ide_db::line_index;
use load_cargo::{LoadCargoConfig, ProcMacroServerChoice, load_workspace_at};
use rustc_hash::{FxHashMap, FxHashSet};
use scip::types::{self as scip_types, SymbolInformation};
use tracing::error;
use vfs::FileId;

use crate::{
    cli::flags,
    config::ConfigChange,
    line_index::{LineEndings, LineIndex, PositionEncoding},
};

impl flags::Scip {
    pub fn run(self) -> anyhow::Result<()> {
        eprintln!("Generating SCIP start...");
        let now = Instant::now();

        let no_progress = &|s| eprintln!("rust-analyzer: Loading {s}");
        let root =
            vfs::AbsPathBuf::assert_utf8(std::env::current_dir()?.join(&self.path)).normalize();

        let mut config = crate::config::Config::new(
            root.clone(),
            lsp_types::ClientCapabilities::default(),
            vec![],
            None,
        );

        if let Some(p) = self.config_path {
            let mut file = std::io::BufReader::new(std::fs::File::open(p)?);
            let json = serde_json::from_reader(&mut file)?;
            let mut change = ConfigChange::default();
            change.change_client_config(json);

            let error_sink;
            (config, error_sink, _) = config.apply_change(change);

            // FIXME @alibektas : What happens to errors without logging?
            error!(?error_sink, "Config Error(s)");
        }
        let load_cargo_config = LoadCargoConfig {
            load_out_dirs_from_check: true,
            with_proc_macro_server: ProcMacroServerChoice::Sysroot,
            prefill_caches: true,
            num_worker_threads: self.num_threads.unwrap_or_else(num_cpus::get_physical),
            proc_macro_processes: config.proc_macro_num_processes(),
        };
        let cargo_config = config.cargo(None);
        let (db, vfs, _) = load_workspace_at(
            root.as_path().as_ref(),
            &cargo_config,
            &load_cargo_config,
            &no_progress,
        )?;
        let host = AnalysisHost::with_database(db);
        let db = host.raw_database();
        let analysis = host.analysis();

        let vendored_libs_config = if self.exclude_vendored_libraries {
            VendoredLibrariesConfig::Excluded
        } else {
            VendoredLibrariesConfig::Included { workspace_root: &root.clone().into() }
        };

        let si = StaticIndex::compute(&analysis, vendored_libs_config);

        let metadata = scip_types::Metadata {
            version: scip_types::ProtocolVersion::UnspecifiedProtocolVersion.into(),
            tool_info: Some(scip_types::ToolInfo {
                name: "rust-analyzer".to_owned(),
                version: format!("{}", crate::version::version()),
                arguments: vec![],
                special_fields: Default::default(),
            })
            .into(),
            project_root: format!("file://{root}"),
            text_document_encoding: scip_types::TextEncoding::UTF8.into(),
            special_fields: Default::default(),
        };

        let mut documents = Vec::new();

        // All TokenIds where an Occurrence has been emitted that references a symbol.
        let mut token_ids_referenced: FxHashSet<TokenId> = FxHashSet::default();
        // All TokenIds where the SymbolInformation has been written to the document.
        let mut token_ids_emitted: FxHashSet<TokenId> = FxHashSet::default();
        // All FileIds emitted as documents.
        let mut file_ids_emitted: FxHashSet<FileId> = FxHashSet::default();

        // All non-local symbols encountered, for detecting duplicate symbol errors.
        let mut nonlocal_symbols_emitted: FxHashSet<String> = FxHashSet::default();
        // List of (source_location, symbol) for duplicate symbol errors to report.
        let mut duplicate_symbol_errors: Vec<(String, String)> = Vec::new();
        // This is called after definitions have been deduplicated by token_ids_emitted. The purpose
        // is to detect reuse of symbol names because this causes ambiguity about their meaning.
        let mut record_error_if_symbol_already_used =
            |symbol: String,
             is_inherent_impl: bool,
             relative_path: &str,
             line_index: &LineIndex,
             text_range: TextRange| {
                let is_local = symbol.starts_with("local ");
                if !is_local && !nonlocal_symbols_emitted.insert(symbol.clone()) {
                    if is_inherent_impl {
                        // FIXME: See #18772. Duplicate SymbolInformation for inherent impls is
                        // omitted. It would be preferable to emit them with numbers with
                        // disambiguation, but this is more complex to implement.
                        false
                    } else {
                        let source_location =
                            text_range_to_string(relative_path, line_index, text_range);
                        duplicate_symbol_errors.push((source_location, symbol));
                        // Keep duplicate SymbolInformation. This behavior is preferred over
                        // omitting so that the issue might be visible within downstream tools.
                        true
                    }
                } else {
                    true
                }
            };

        // Generates symbols from token monikers.
        let mut symbol_generator = SymbolGenerator::default();

        for StaticIndexedFile { file_id, tokens, .. } in si.files {
            symbol_generator.clear_document_local_state();

            let Some(relative_path) = get_relative_filepath(&vfs, &root, file_id) else { continue };
            let line_index = get_line_index(db, file_id);

            let mut occurrences = Vec::new();
            let mut symbols = Vec::new();

            for (text_range, id) in tokens.into_iter() {
                let token = si.tokens.get(id).unwrap();

                let Some(TokenSymbols { symbol, enclosing_symbol, is_inherent_impl }) =
                    symbol_generator.token_symbols(id, token)
                else {
                    // token did not have a moniker, so there is no reasonable occurrence to emit
                    // see ide::moniker::def_to_moniker
                    continue;
                };

                let is_defined_in_this_document = match token.definition {
                    Some(def) => def.file_id == file_id,
                    _ => false,
                };
                if is_defined_in_this_document {
                    if token_ids_emitted.insert(id) {
                        // token_ids_emitted does deduplication. This checks that this results
                        // in unique emitted symbols, as otherwise references are ambiguous.
                        let should_emit = record_error_if_symbol_already_used(
                            symbol.clone(),
                            is_inherent_impl,
                            relative_path.as_str(),
                            &line_index,
                            text_range,
                        );
                        if should_emit {
                            symbols.push(compute_symbol_info(
                                symbol.clone(),
                                enclosing_symbol,
                                token,
                            ));
                        }
                    }
                } else {
                    token_ids_referenced.insert(id);
                }

                // If the range of the def and the range of the token are the same, this must be the definition.
                // they also must be in the same file. See https://github.com/rust-lang/rust-analyzer/pull/17988
                let is_definition = match token.definition {
                    Some(def) => def.file_id == file_id && def.range == text_range,
                    _ => false,
                };

                let mut symbol_roles = Default::default();
                if is_definition {
                    symbol_roles |= scip_types::SymbolRole::Definition as i32;
                }

                let enclosing_range = match token.definition_body {
                    Some(def_body) if def_body.file_id == file_id => {
                        text_range_to_scip_range(&line_index, def_body.range)
                    }
                    _ => Vec::new(),
                };

                occurrences.push(scip_types::Occurrence {
                    range: text_range_to_scip_range(&line_index, text_range),
                    symbol,
                    symbol_roles,
                    override_documentation: Vec::new(),
                    syntax_kind: Default::default(),
                    diagnostics: Vec::new(),
                    special_fields: Default::default(),
                    enclosing_range,
                });
            }

            if occurrences.is_empty() {
                continue;
            }

            let position_encoding =
                scip_types::PositionEncoding::UTF8CodeUnitOffsetFromLineStart.into();
            documents.push(scip_types::Document {
                relative_path,
                language: "rust".to_owned(),
                occurrences,
                symbols,
                text: String::new(),
                position_encoding,
                special_fields: Default::default(),
            });
            if !file_ids_emitted.insert(file_id) {
                panic!("Invariant violation: file emitted multiple times.");
            }
        }

        // Collect all symbols referenced by the files but not defined within them.
        let mut external_symbols = Vec::new();
        for id in token_ids_referenced.difference(&token_ids_emitted) {
            let id = *id;
            let token = si.tokens.get(id).unwrap();

            let Some(definition) = token.definition else {
                continue;
            };

            let file_id = definition.file_id;
            let Some(relative_path) = get_relative_filepath(&vfs, &root, file_id) else { continue };
            let line_index = get_line_index(db, file_id);
            let text_range = definition.range;
            if file_ids_emitted.contains(&file_id) {
                tracing::error!(
                    "Bug: definition at {} should have been in an SCIP document but was not.",
                    text_range_to_string(relative_path.as_str(), &line_index, text_range)
                );
                continue;
            }

            let TokenSymbols { symbol, enclosing_symbol, .. } = symbol_generator
                .token_symbols(id, token)
                .expect("To have been referenced, the symbol must be in the cache.");

            record_error_if_symbol_already_used(
                symbol.clone(),
                false,
                relative_path.as_str(),
                &line_index,
                text_range,
            );
            external_symbols.push(compute_symbol_info(symbol.clone(), enclosing_symbol, token));
        }

        let index = scip_types::Index {
            metadata: Some(metadata).into(),
            documents,
            external_symbols,
            special_fields: Default::default(),
        };

        if !duplicate_symbol_errors.is_empty() {
            eprintln!("{DUPLICATE_SYMBOLS_MESSAGE}");
            for (source_location, symbol) in duplicate_symbol_errors {
                eprintln!("{source_location}");
                eprintln!("  Duplicate symbol: {symbol}");
                eprintln!();
            }
        }

        let out_path = self.output.unwrap_or_else(|| PathBuf::from(r"index.scip"));
        scip::write_message_to_file(out_path, index)
            .map_err(|err| anyhow::format_err!("Failed to write scip to file: {}", err))?;

        eprintln!("Generating SCIP finished {:?}", now.elapsed());
        Ok(())
    }
}

// FIXME: Known buggy cases are described here.
const DUPLICATE_SYMBOLS_MESSAGE: &str = "
Encountered duplicate scip symbols, indicating an internal rust-analyzer bug. These duplicates are
included in the output, but this causes information lookup to be ambiguous and so information about
these symbols presented by downstream tools may be incorrect.

Known rust-analyzer bugs that can cause this:

  * Definitions in crate example binaries which have the same symbol as definitions in the library
    or some other example.

  * Struct/enum/const/static/impl definitions nested in a function do not mention the function name.
    See #18771.

Duplicate symbols encountered:
";

fn compute_symbol_info(
    symbol: String,
    enclosing_symbol: Option<String>,
    token: &TokenStaticData,
) -> SymbolInformation {
    let documentation = match &token.documentation {
        Some(doc) => vec![doc.as_str().to_owned()],
        None => vec![],
    };

    let position_encoding = scip_types::PositionEncoding::UTF8CodeUnitOffsetFromLineStart.into();
    let signature_documentation = token.signature.clone().map(|text| scip_types::Document {
        relative_path: "".to_owned(),
        language: "rust".to_owned(),
        text,
        position_encoding,
        ..Default::default()
    });
    scip_types::SymbolInformation {
        symbol,
        documentation,
        relationships: implementation_relationships(token),
        special_fields: Default::default(),
        kind: symbol_kind(token.kind).into(),
        display_name: token.display_name.clone().unwrap_or_default(),
        signature_documentation: signature_documentation.into(),
        enclosing_symbol: enclosing_symbol.unwrap_or_default(),
    }
}

/// `is_implementation` relationships from `TokenStaticData::implements`,
/// sorted and deduplicated so the output is deterministic (`Ord for String` is
/// bytewise, so the order is locale-independent). A local moniker cannot be a
/// cross-document relationship target and is skipped.
fn implementation_relationships(token: &TokenStaticData) -> Vec<scip_types::Relationship> {
    let mut symbols: Vec<String> = token
        .implements
        .iter()
        .filter_map(|m| match m {
            MonikerResult::Moniker(moniker) => {
                Some(scip::symbol::format_symbol(moniker_to_symbol(moniker)))
            }
            MonikerResult::Local { .. } => None,
        })
        .collect();
    symbols.sort();
    symbols.dedup();
    symbols
        .into_iter()
        .map(|symbol| scip_types::Relationship {
            symbol,
            is_implementation: true,
            ..Default::default()
        })
        .collect()
}

fn get_relative_filepath(
    vfs: &vfs::Vfs,
    rootpath: &vfs::AbsPathBuf,
    file_id: ide::FileId,
) -> Option<String> {
    Some(vfs.file_path(file_id).as_path()?.strip_prefix(rootpath)?.as_str().to_owned())
}

fn get_line_index(db: &RootDatabase, file_id: FileId) -> LineIndex {
    LineIndex {
        index: line_index(db, file_id).clone(),
        encoding: PositionEncoding::Utf8,
        endings: LineEndings::Unix,
    }
}

// SCIP Ranges have a (very large) optimization that ranges if they are on the same line
// only encode as a vector of [start_line, start_col, end_col].
//
// This transforms a line index into the optimized SCIP Range.
fn text_range_to_scip_range(line_index: &LineIndex, range: TextRange) -> Vec<i32> {
    let LineCol { line: start_line, col: start_col } = line_index.index.line_col(range.start());
    let LineCol { line: end_line, col: end_col } = line_index.index.line_col(range.end());

    if start_line == end_line {
        vec![start_line as i32, start_col as i32, end_col as i32]
    } else {
        vec![start_line as i32, start_col as i32, end_line as i32, end_col as i32]
    }
}

fn text_range_to_string(relative_path: &str, line_index: &LineIndex, range: TextRange) -> String {
    let LineCol { line: start_line, col: start_col } = line_index.index.line_col(range.start());
    let LineCol { line: end_line, col: end_col } = line_index.index.line_col(range.end());

    format!("{relative_path}:{start_line}:{start_col}-{end_line}:{end_col}")
}

fn new_descriptor_str(
    name: &str,
    suffix: scip_types::descriptor::Suffix,
) -> scip_types::Descriptor {
    scip_types::Descriptor {
        name: name.to_owned(),
        disambiguator: "".to_owned(),
        suffix: suffix.into(),
        special_fields: Default::default(),
    }
}

fn symbol_kind(kind: SymbolInformationKind) -> scip_types::symbol_information::Kind {
    use scip_types::symbol_information::Kind as ScipKind;
    match kind {
        SymbolInformationKind::AssociatedType => ScipKind::AssociatedType,
        SymbolInformationKind::Attribute => ScipKind::Attribute,
        SymbolInformationKind::Constant => ScipKind::Constant,
        SymbolInformationKind::Enum => ScipKind::Enum,
        SymbolInformationKind::EnumMember => ScipKind::EnumMember,
        SymbolInformationKind::Field => ScipKind::Field,
        SymbolInformationKind::Function => ScipKind::Function,
        SymbolInformationKind::Macro => ScipKind::Macro,
        SymbolInformationKind::Method => ScipKind::Method,
        SymbolInformationKind::Module => ScipKind::Module,
        SymbolInformationKind::Parameter => ScipKind::Parameter,
        SymbolInformationKind::SelfParameter => ScipKind::SelfParameter,
        SymbolInformationKind::StaticMethod => ScipKind::StaticMethod,
        SymbolInformationKind::StaticVariable => ScipKind::StaticVariable,
        SymbolInformationKind::Struct => ScipKind::Struct,
        SymbolInformationKind::Trait => ScipKind::Trait,
        SymbolInformationKind::TraitMethod => ScipKind::TraitMethod,
        SymbolInformationKind::Type => ScipKind::Type,
        SymbolInformationKind::TypeAlias => ScipKind::TypeAlias,
        SymbolInformationKind::TypeParameter => ScipKind::TypeParameter,
        SymbolInformationKind::Union => ScipKind::Union,
        SymbolInformationKind::Variable => ScipKind::Variable,
    }
}

#[derive(Clone)]
struct TokenSymbols {
    symbol: String,
    /// Definition that contains this one. Only set when `symbol` is local.
    enclosing_symbol: Option<String>,
    /// True if this symbol is for an inherent impl. This is used to only emit `SymbolInformation`
    /// for a struct's first inherent impl, since their symbol names are not disambiguated.
    is_inherent_impl: bool,
}

#[derive(Default)]
struct SymbolGenerator {
    token_to_symbols: FxHashMap<TokenId, Option<TokenSymbols>>,
    local_count: usize,
}

impl SymbolGenerator {
    fn clear_document_local_state(&mut self) {
        self.local_count = 0;
    }

    fn token_symbols(&mut self, id: TokenId, token: &TokenStaticData) -> Option<TokenSymbols> {
        let mut local_count = self.local_count;
        let token_symbols = self
            .token_to_symbols
            .entry(id)
            .or_insert_with(|| {
                Some(match token.moniker.as_ref()? {
                    MonikerResult::Moniker(moniker) => TokenSymbols {
                        symbol: scip::symbol::format_symbol(moniker_to_symbol(moniker)),
                        enclosing_symbol: None,
                        is_inherent_impl: match &moniker.identifier.description[..] {
                            // inherent impls are represented as impl#[SelfType]
                            [.., descriptor, _] => {
                                descriptor.desc == MonikerDescriptorKind::Type
                                    && descriptor.name == "impl"
                            }
                            _ => false,
                        },
                    },
                    MonikerResult::Local { enclosing_moniker } => {
                        let local_symbol = scip::types::Symbol::new_local(local_count);
                        local_count += 1;
                        TokenSymbols {
                            symbol: scip::symbol::format_symbol(local_symbol),
                            enclosing_symbol: enclosing_moniker
                                .as_ref()
                                .map(moniker_to_symbol)
                                .map(scip::symbol::format_symbol),
                            is_inherent_impl: false,
                        }
                    }
                })
            })
            .clone();
        self.local_count = local_count;
        token_symbols
    }
}

fn moniker_to_symbol(moniker: &Moniker) -> scip_types::Symbol {
    let PackageInformation { name, version, target, repo: _ } = &moniker.package_information;
    // A cargo package is several crates -- the lib, each bin, each integration test, each bench,
    // each example, `build.rs` -- and only the package name reached the symbol, so items of two
    // targets of one package shared one symbol string. `ide` decides WHICH target has to be named
    // (`None` for a lib, and for any project model with no targets); the spelling is decided here.
    //
    // It goes in the PACKAGE field, not in a descriptor: a descriptor named after a target collides
    // with a real module of that name (`tests/test_de.rs` and `src/test_de.rs` in one package), while
    // the package field cannot collide with anything inside a crate. `:` separates it because scip
    // splits a symbol on spaces only, so the field stays one token and remains greppable as
    // `serde_test_suite:test_de`.
    let package_name = match target {
        Some(target) => format!("{name}:{target}"),
        None => name.clone(),
    };
    scip_types::Symbol {
        scheme: "rust-analyzer".into(),
        package: Some(scip_types::Package {
            manager: "cargo".to_owned(),
            name: package_name,
            version: version.clone().unwrap_or_else(|| ".".to_owned()),
            special_fields: Default::default(),
        })
        .into(),
        descriptors: moniker_descriptors(&moniker.identifier),
        special_fields: Default::default(),
    }
}

fn moniker_descriptors(identifier: &MonikerIdentifier) -> Vec<scip_types::Descriptor> {
    use scip_types::descriptor::Suffix::*;
    identifier
        .description
        .iter()
        .map(|desc| {
            new_descriptor_str(
                &desc.name,
                match desc.desc {
                    MonikerDescriptorKind::Namespace => Namespace,
                    MonikerDescriptorKind::Type => Type,
                    MonikerDescriptorKind::Term => Term,
                    MonikerDescriptorKind::Method => Method,
                    MonikerDescriptorKind::TypeParameter => TypeParameter,
                    MonikerDescriptorKind::Parameter => Parameter,
                    MonikerDescriptorKind::Macro => Macro,
                    MonikerDescriptorKind::Meta => Meta,
                },
            )
        })
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;
    use hir::FileRangeWrapper;
    use ide::{FilePosition, TextSize};
    use test_fixture::ChangeFixture;
    use vfs::VfsPath;

    fn position(#[rust_analyzer::rust_fixture] ra_fixture: &str) -> (AnalysisHost, FilePosition) {
        let mut host = AnalysisHost::default();
        let change_fixture = ChangeFixture::parse(ra_fixture);
        host.raw_database_mut().apply_change(change_fixture.change);
        let (file_id, range_or_offset) =
            change_fixture.file_position.expect("expected a marker ()");
        let offset = range_or_offset.expect_offset();
        let position = FilePosition { file_id: file_id.file_id(), offset };
        (host, position)
    }

    /// If expected == "", then assert that there are no symbols (this is basically local symbol)
    #[track_caller]
    fn check_symbol(#[rust_analyzer::rust_fixture] ra_fixture: &str, expected: &str) {
        let (host, position) = position(ra_fixture);

        let analysis = host.analysis();
        let si = StaticIndex::compute(
            &analysis,
            VendoredLibrariesConfig::Included {
                workspace_root: &VfsPath::new_virtual_path("/workspace".to_owned()),
            },
        );

        let FilePosition { file_id, offset } = position;

        let mut found_symbol = None;
        for file in &si.files {
            if file.file_id != file_id {
                continue;
            }
            for &(range, id) in &file.tokens {
                // check if cursor is within token, ignoring token for the module defined by the file (whose range is the whole file)
                if range.start() != TextSize::from(0) && range.contains(offset - TextSize::from(1))
                {
                    let token = si.tokens.get(id).unwrap();
                    found_symbol = match token.moniker.as_ref() {
                        None => None,
                        Some(MonikerResult::Moniker(moniker)) => {
                            Some(scip::symbol::format_symbol(moniker_to_symbol(moniker)))
                        }
                        Some(MonikerResult::Local { enclosing_moniker: Some(moniker) }) => {
                            Some(format!(
                                "local enclosed by {}",
                                scip::symbol::format_symbol(moniker_to_symbol(moniker))
                            ))
                        }
                        Some(MonikerResult::Local { enclosing_moniker: None }) => {
                            Some("unenclosed local".to_owned())
                        }
                    };
                    break;
                }
            }
        }

        if expected.is_empty() {
            assert!(found_symbol.is_none(), "must have no symbols {found_symbol:?}");
            return;
        }

        assert!(found_symbol.is_some(), "must have one symbol {found_symbol:?}");
        assert_eq!(found_symbol.unwrap(), expected);
    }

    /// The sorted `is_implementation` targets of the token at the cursor.
    fn check_relationships(#[rust_analyzer::rust_fixture] ra_fixture: &str, expected: &[&str]) {
        let (host, position) = position(ra_fixture);
        let analysis = host.analysis();
        let si = StaticIndex::compute(
            &analysis,
            VendoredLibrariesConfig::Included {
                workspace_root: &VfsPath::new_virtual_path("/workspace".to_owned()),
            },
        );
        let FilePosition { file_id, offset } = position;
        let mut found: Option<Vec<String>> = None;
        for file in &si.files {
            if file.file_id != file_id {
                continue;
            }
            for &(range, id) in &file.tokens {
                if range.start() != TextSize::from(0) && range.contains(offset - TextSize::from(1))
                {
                    let token = si.tokens.get(id).unwrap();
                    found = Some(
                        implementation_relationships(token)
                            .into_iter()
                            .inspect(|r| assert!(r.is_implementation))
                            .map(|r| r.symbol)
                            .collect(),
                    );
                    break;
                }
            }
        }
        let found = found.expect("no token at the cursor");
        assert_eq!(found, expected.iter().map(|s| s.to_string()).collect::<Vec<_>>());
    }

    #[test]
    fn relationships_adt_with_trait_impl() {
        check_relationships(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub trait Area { fn area(&self) -> u32; }
pub trait Named {}
pub struct Square$0;
impl Area for Square { fn area(&self) -> u32 { 1 } }
impl Named for Square {}
"#,
            &["rust-analyzer cargo foo 0.1.0 Area#", "rust-analyzer cargo foo 0.1.0 Named#"],
        );
    }

    #[test]
    fn relationships_trait_impl_method() {
        check_relationships(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub trait Area { fn area(&self) -> u32; }
pub struct Square;
impl Area for Square { fn area$0(&self) -> u32 { 1 } }
"#,
            &["rust-analyzer cargo foo 0.1.0 Area#area()."],
        );
    }

    #[test]
    fn relationships_no_blanket_impl_on_adt() {
        // Pins the absence: all_for_type returns non-blanket impls only. If
        // that ever widens, every ADT would gain an edge to every blanket trait.
        // `Real` is a positive control: the test cannot pass unless the cursor
        // really is on `Plain` (an empty list on the wrong token would).
        check_relationships(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub trait Describe { fn describe(&self) -> u32; }
pub trait Real {}
impl<T> Describe for T { fn describe(&self) -> u32 { 0 } }
impl Real for Plain {}
pub struct Plain$0;
"#,
            &["rust-analyzer cargo foo 0.1.0 Real#"],
        );
    }

    #[test]
    fn relationships_no_blanket_impl_on_adt_from_dependency() {
        // The same pin across crates: a blanket impl in a dependency, which is
        // the dependency-graph fan-out the absence protects against.
        // `dep::Other` is a control for the dependency edge: it resolves only
        // through `deps:dep`, so a fixture whose edge is missing cannot pass,
        // and the absence of `Describe` is then an absence across a live edge.
        check_relationships(
            r#"
//- /dep/lib.rs crate:dep@0.1.0,https://a.b/dep.git library
pub trait Describe { fn describe(&self) -> u32; }
pub trait Other {}
impl<T> Describe for T { fn describe(&self) -> u32 { 0 } }
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git deps:dep library
pub trait Real {}
impl Real for Plain {}
impl dep::Other for Plain {}
pub struct Plain$0;
"#,
            &["rust-analyzer cargo dep 0.1.0 Other#", "rust-analyzer cargo foo 0.1.0 Real#"],
        );
    }

    #[test]
    fn blanket_method_from_dependency_applies_to_plain() {
        // The companion of relationships_no_blanket_impl_on_adt_from_dependency:
        // dep's blanket impl DOES apply to Plain across the edge (the call
        // resolves to the impl's method), so the absence of a type-level
        // Describe edge there is an absence of an edge, not of an applicable
        // impl.
        check_symbol(
            r#"
//- /dep/lib.rs crate:dep@0.1.0,https://a.b/dep.git library
pub trait Describe { fn describe(&self) -> u32; }
pub trait Other {}
impl<T> Describe for T { fn describe(&self) -> u32 { 0 } }
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git deps:dep library
use dep::Describe;
pub trait Real {}
impl Real for Plain {}
impl dep::Other for Plain {}
pub struct Plain;
pub fn f(r: Plain) -> u32 { r.describe$0() }
"#,
            "rust-analyzer cargo dep 0.1.0 impl#[T][Describe]describe().",
        );
    }

    #[test]
    fn blanket_method_from_dependency_needs_the_edge() {
        // Without `deps:dep` the same call resolves to nothing: the resolution
        // above goes through the dependency edge. check_symbol cannot tell "no
        // token at the cursor" from "a token without a moniker", so this pins
        // that the edge is load-bearing, not which of the two happens without it.
        check_symbol(
            r#"
//- /dep/lib.rs crate:dep@0.1.0,https://a.b/dep.git library
pub trait Describe { fn describe(&self) -> u32; }
pub trait Other {}
impl<T> Describe for T { fn describe(&self) -> u32 { 0 } }
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
use dep::Describe;
pub trait Real {}
impl Real for Plain {}
impl dep::Other for Plain {}
pub struct Plain;
pub fn f(r: Plain) -> u32 { r.describe$0() }
"#,
            "",
        );
    }

    #[test]
    fn relationships_blanket_impl_method() {
        check_relationships(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub trait Describe { fn describe(&self) -> u32; }
impl<T> Describe for T { fn describe$0(&self) -> u32 { 0 } }
"#,
            &["rust-analyzer cargo foo 0.1.0 Describe#describe()."],
        );
    }

    #[test]
    fn relationships_inherent_impl_has_none() {
        check_relationships(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub struct Square;
impl Square { pub fn side$0(&self) -> u32 { 1 } }
"#,
            &[],
        );
    }

    #[test]
    fn basic() {
        check_symbol(
            r#"
//- /workspace/lib.rs crate:main deps:foo
use foo::example_mod::func;
fn main() {
    func$0();
}
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod example_mod {
    pub fn func() {}
}
"#,
            "rust-analyzer cargo foo 0.1.0 example_mod/func().",
        );
    }

    #[test]
    fn operator_overload() {
        check_symbol(
            r#"
//- minicore: add
//- /workspace/lib.rs crate:main
use core::ops::AddAssign;

struct S;

impl AddAssign for S {
    fn add_assign(&mut self, _rhs: Self) {}
}

fn main() {
    let mut s = S;
    s +=$0 S;
}
"#,
            "rust-analyzer cargo main . impl#[S][`AddAssign<Self>`]add_assign().",
        );
    }

    #[test]
    fn symbol_for_trait() {
        check_symbol(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod module {
    pub trait MyTrait {
        pub fn func$0() {}
    }
}
"#,
            "rust-analyzer cargo foo 0.1.0 module/MyTrait#func().",
        );
    }

    #[test]
    fn symbol_for_trait_alias() {
        check_symbol(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
#![feature(trait_alias)]
pub mod module {
    pub trait MyTrait {}
    pub trait MyTraitAlias$0 = MyTrait;
}
"#,
            "rust-analyzer cargo foo 0.1.0 module/MyTraitAlias#",
        );
    }

    #[test]
    fn symbol_for_trait_constant() {
        check_symbol(
            r#"
    //- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
    pub mod module {
        pub trait MyTrait {
            const MY_CONST$0: u8;
        }
    }
    "#,
            "rust-analyzer cargo foo 0.1.0 module/MyTrait#MY_CONST.",
        );
    }

    #[test]
    fn symbol_for_trait_type() {
        check_symbol(
            r#"
    //- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
    pub mod module {
        pub trait MyTrait {
            type MyType$0;
        }
    }
    "#,
            "rust-analyzer cargo foo 0.1.0 module/MyTrait#MyType#",
        );
    }

    #[test]
    fn symbol_for_trait_impl_function() {
        check_symbol(
            r#"
    //- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
    pub mod module {
        pub trait MyTrait {
            pub fn func() {}
        }

        struct MyStruct {}

        impl MyTrait for MyStruct {
            pub fn func$0() {}
        }
    }
    "#,
            "rust-analyzer cargo foo 0.1.0 module/impl#[MyStruct][MyTrait]func().",
        );
    }

    #[test]
    fn symbol_for_field() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main deps:foo
    use foo::St;
    fn main() {
        let x = St { a$0: 2 };
    }
    //- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
    pub struct St {
        pub a: i32,
    }
    "#,
            "rust-analyzer cargo foo 0.1.0 St#a.",
        );
    }

    #[test]
    fn symbol_for_param() {
        check_symbol(
            r#"
//- /workspace/lib.rs crate:main deps:foo
use foo::example_mod::func;
fn main() {
    func(42);
}
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod example_mod {
    pub fn func(x$0: usize) {}
}
"#,
            "local enclosed by rust-analyzer cargo foo 0.1.0 example_mod/func().",
        );
    }

    #[test]
    fn symbol_for_closure_param() {
        check_symbol(
            r#"
//- /workspace/lib.rs crate:main deps:foo
use foo::example_mod::func;
fn main() {
    func();
}
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod example_mod {
    pub fn func() {
        let f = |x$0: usize| {};
    }
}
"#,
            "local enclosed by rust-analyzer cargo foo 0.1.0 example_mod/func().",
        );
    }

    #[test]
    fn local_symbol_for_local() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main deps:foo
    use foo::module::func;
    fn main() {
        func();
    }
    //- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
    pub mod module {
        pub fn func() {
            let x$0 = 2;
        }
    }
    "#,
            "local enclosed by rust-analyzer cargo foo 0.1.0 module/func().",
        );
    }

    #[test]
    fn global_symbol_for_pub_struct() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    mod foo;

    fn main() {
        let _bar = foo::Bar { i: 0 };
    }
    //- /workspace/foo.rs
    pub struct Bar$0 {
        pub i: i32,
    }
    "#,
            "rust-analyzer cargo main . foo/Bar#",
        );
    }

    #[test]
    fn global_symbol_for_pub_struct_reference() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    mod foo;

    fn main() {
        let _bar = foo::Bar$0 { i: 0 };
    }
    //- /workspace/foo.rs
    pub struct Bar {
        pub i: i32,
    }
    "#,
            "rust-analyzer cargo main . foo/Bar#",
        );
    }

    #[test]
    fn symbol_for_type_alias() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub type MyTypeAlias$0 = u8;
    "#,
            "rust-analyzer cargo main . MyTypeAlias#",
        );
    }

    // These four used to be marked `// FIXME: This test represents current misbehavior` and to
    // expect the bare module-level symbol, with the suggested repair being to make these items
    // *locals* (`local enclosed by ... func().`). This fork takes the other repair: the enclosing
    // function becomes part of the descriptor, so the item keeps a global symbol and that symbol is
    // unique.
    //
    // NOT because the locals repair loses anything in SCIP. A `local ...` symbol is a well-formed
    // SCIP symbol; SCIP's occurrence model is per document, and a consumer that resolves a reference
    // inside the document it is reading follows a local symbol as well as a global one. Both repairs
    // close exactly the same collisions.
    //
    // The reason is this fork's own consumer. Alexandria joins relationship edges ACROSS documents by
    // symbol string: a fn-local type can implement a trait, and that `is_implementation` edge has to
    // match a symbol emitted by whichever document defines the trait. A local symbol is unique only
    // within the document that emits it, so there is nothing for the loader to match it against and
    // the edge is dropped -- from the one plane this fork exists to fill. A qualified global symbol
    // disambiguates and stays joinable.
    //
    // So this is a consumer requirement, not a defect in the alternative. If upstream ever makes
    // these locals, these expectations are the ones to revisit.
    #[test]
    fn symbol_for_nested_function() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       pub fn inner_func$0() {}
    }
    "#,
            "rust-analyzer cargo main . func().inner_func().",
        );
    }

    #[test]
    fn symbol_for_struct_in_function() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       struct SomeStruct$0 {}
    }
    "#,
            "rust-analyzer cargo main . func().SomeStruct#",
        );
    }

    #[test]
    fn symbol_for_const_in_function() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       const SOME_CONST$0: u32 = 1;
    }
    "#,
            "rust-analyzer cargo main . func().SOME_CONST.",
        );
    }

    #[test]
    fn symbol_for_static_in_function() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       static SOME_STATIC$0: u32 = 1;
    }
    "#,
            "rust-analyzer cargo main . func().SOME_STATIC.",
        );
    }

    /// The defect this fork's descriptor change exists for: two functions in ONE module each
    /// defining `FieldVisitor` computed ONE symbol string, so a consumer received one record for two
    /// unrelated types. Both halves of the pair are asserted, because a test that only pins one of
    /// them passes just as well when the other is the string it collides with.
    #[test]
    fn fn_local_structs_of_one_name_in_two_fns_are_distinct_a() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn de_a() {
       struct FieldVisitor$0;
    }
    pub fn de_b() {
       struct FieldVisitor;
    }
    "#,
            "rust-analyzer cargo main . de_a().FieldVisitor#",
        );
    }

    #[test]
    fn fn_local_structs_of_one_name_in_two_fns_are_distinct_b() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn de_a() {
       struct FieldVisitor;
    }
    pub fn de_b() {
       struct FieldVisitor$0;
    }
    "#,
            "rust-analyzer cargo main . de_b().FieldVisitor#",
        );
    }

    /// The shape that motivated the fix, from a real corpus: `tokio 1.53.1 DATA.` had 13 definition
    /// sites, all 13 inside a function body, in 2 documents -- a `const DATA` declared separately in
    /// thirteen tests. A const in a fn and a struct in two fns are each covered above; this is the
    /// combination that was actually observed.
    #[test]
    fn fn_local_consts_of_one_name_in_two_fns_are_distinct_a() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn read_a() {
       const DATA$0: &[u8] = b"a";
    }
    pub fn read_b() {
       const DATA: &[u8] = b"b";
    }
    "#,
            "rust-analyzer cargo main . read_a().DATA.",
        );
    }

    #[test]
    fn fn_local_consts_of_one_name_in_two_fns_are_distinct_b() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn read_a() {
       const DATA: &[u8] = b"a";
    }
    pub fn read_b() {
       const DATA$0: &[u8] = b"b";
    }
    "#,
            "rust-analyzer cargo main . read_b().DATA.",
        );
    }

    /// A reference inside one function must resolve to THAT function's item. Without this, the
    /// definitions could be distinct while every use still pointed at one of them -- the two are
    /// separate properties and the first does not imply the second.
    #[test]
    fn reference_to_fn_local_struct_resolves_within_its_own_fn() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn de_a() {
       struct FieldVisitor;
    }
    pub fn de_b() {
       struct FieldVisitor;
       let _v = FieldVisitor$0;
    }
    "#,
            "rust-analyzer cargo main . de_b().FieldVisitor#",
        );
    }

    /// Same name, different item kinds, in two functions. The kind suffix (`#` for both a struct and
    /// an enum) does not separate these, so the function descriptor is doing the whole job.
    #[test]
    fn fn_local_struct_and_enum_of_one_name_are_distinct() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn de_a() {
       struct Repr;
    }
    pub fn de_b() {
       enum Repr$0 {}
    }
    "#,
            "rust-analyzer cargo main . de_b().Repr#",
        );
    }

    /// An item in a `const`/`static` initializer block, which is also a block module. `const _` has
    /// no name, so that shape is NOT disambiguated -- see `fn_local_item_in_anonymous_const_is_not_disambiguated`.
    #[test]
    fn symbol_for_struct_in_named_const_initializer() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub const TABLE: u8 = {
       struct Helper$0;
       0
    };
    "#,
            "rust-analyzer cargo main . TABLE.Helper#",
        );
    }

    /// A KNOWN RESIDUAL, asserted so it is a recorded limitation rather than a surprise: `const _`
    /// contributes no name, so two items of one name in two anonymous consts still collide. This is
    /// the shape derive macros emit. Naming them by position would be worse -- a positional index is
    /// not stable across edits, so every symbol below an insertion would churn.
    #[test]
    fn fn_local_item_in_anonymous_const_is_not_disambiguated() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    const _: () = {
       struct Helper$0;
    };
    "#,
            "rust-analyzer cargo main . Helper#",
        );
    }

    /// A bare `{ .. }` used as a statement is a block module too, and its own parent is not an item.
    /// This is the test that decided the shape of the fix: with the walk stopping at the block's
    /// immediate parent, this came out as a bare `rust-analyzer cargo main . Helper#` -- no `func()`
    /// at all, so the item could now collide with a module-level `Helper` -- because
    /// `containing_module` of the inner block module goes straight to the enclosing non-block module
    /// and never visits the function's own body block. The walk therefore covers all levels.
    #[test]
    fn struct_in_a_bare_block_inside_a_fn_is_qualified_by_the_fn() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       { struct Helper$0; }
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// The other half of that decision, and the case that rules out simply walking every ancestor:
    /// here the caller's own module chain DOES reach `outer`'s body block, so a full ancestor walk
    /// named `outer` twice and produced `outer().outer().inner().S#`. Both this and the bare-block
    /// test above pass only if the walk stops at the first `Item` ancestor.
    #[test]
    fn struct_in_a_fn_in_a_fn_names_both_fns() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn outer() {
       fn inner() {
           struct S$0;
       }
    }
    "#,
            "rust-analyzer cargo main . outer().inner().S#",
        );
    }

    /// A KNOWN RESIDUAL: two blocks in ONE function. The function name is the only disambiguator, so
    /// this pair is still ambiguous. Recorded rather than fixed -- positions are not stable across
    /// edits. The same applies to two closures in one function.
    ///
    /// The claim is an EQUALITY, so both halves are asserted against the SAME string. Pinning only
    /// the first half would keep passing if the second half moved, which is precisely the change that
    /// would retire this residual.
    #[test]
    fn two_blocks_in_one_fn_are_not_disambiguated() {
        let both = "rust-analyzer cargo main . func().Helper#";
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       { struct Helper$0; }
       { struct Helper; }
    }
    "#,
            both,
        );
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       { struct Helper; }
       { struct Helper$0; }
    }
    "#,
            both,
        );
    }

    /// The `impl` an associated fn belongs to is named, so a fn-local item under `impl A` and under
    /// `impl B` no longer collide. The caller's own walk cannot reach the impl: a block module's
    /// parent is the module the impl lives in, so without this the pair was both `m().Helper#`.
    ///
    /// The impl is spelled by the same hir renderer the `Definition::SelfType` arm uses, in the same
    /// order (`impl`, self type, then trait for a trait impl), so this agrees with the impl's own
    /// symbol rather than being a second syntax-derived spelling of it.
    #[test]
    fn fn_local_item_under_an_impl_is_qualified_by_the_impl() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct A;
    impl A {
       pub fn m() {
           struct Helper$0;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[A]m().Helper#",
        );
    }

    /// The pair the impl descriptor exists for: same fn name, same local item name, two impls. Read
    /// with the test above -- the two expectations differ only in the self type.
    #[test]
    fn fn_local_items_under_two_impls_are_distinct() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct A;
    pub struct B;
    impl A {
       pub fn m() {
           struct Helper$0;
       }
    }
    impl B {
       pub fn m() {
           struct Helper;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[A]m().Helper#",
        );
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct A;
    pub struct B;
    impl A {
       pub fn m() {
           struct Helper;
       }
    }
    impl B {
       pub fn m() {
           struct Helper$0;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[B]m().Helper#",
        );
    }

    /// Review finding m-C, written as a fixture BEFORE any code change so that "does it reproduce" is
    /// answered by the suite and not by reading the renderer. The impl descriptors are rendered with
    /// `display(db, module, ..)` where `module` is the BLOCK module, while the impl's own symbol renders
    /// them against the item's module; a fn-local type shadowing the self type's name is the case where
    /// those two modules could disagree. Both spellings are asserted, so a divergence fails an assertion
    /// instead of producing two symbols nobody compared.
    #[test]
    fn fn_local_item_shadowing_the_self_type_spells_the_impl_like_the_method_does() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct A;
    impl A {
       pub fn m() {
           struct A;
           struct Helper$0;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[A]m().Helper#",
        );
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct A;
    impl A {
       pub fn m$0() {
           struct A;
           struct Helper;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[A]m().",
        );
    }

    /// m-C again, by the route shadowing cannot take, and this is the route that REPRODUCED.
    /// `display_source_code` renders a path that is valid FROM the module it is given, and a block module
    /// sees everything its parent sees plus its own items -- so the two modules can only disagree when a
    /// local item changes which path is shortest. A `use` in the fn body does that and is itself an item,
    /// so it also makes the body a block module. Before the fix this printed `impl#[A]m().Helper#` while
    /// the next test's `m` printed impl#[`sub::A`]m(): a fn-local item whose symbol was NOT its owner's
    /// symbol plus a descriptor. Two separate tests, not two assertions in one, because a divergence has
    /// to print BOTH strings to be useful and the first failing assertion would hide the second.
    #[test]
    fn fn_local_use_shortening_the_self_types_path_spells_the_impl_as_the_method_does() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub mod sub { pub struct A; }
    impl crate::sub::A {
       pub fn m() {
           use crate::sub::A;
           struct Helper$0;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[`sub::A`]m().Helper#",
        );
    }

    #[test]
    fn a_method_over_a_submodule_self_type_spells_the_impl_from_its_own_module() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub mod sub { pub struct A; }
    impl crate::sub::A {
       pub fn m$0() {
           use crate::sub::A;
           struct Helper;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[`sub::A`]m().",
        );
    }

    /// m-C's consequence, which the divergence on its own does not establish: a COLLISION between two
    /// fn-local items, the exact failure the owner chain was added to remove. Two impls for two different
    /// types both named `T`, each method shortening its own self type to `T` inside its own body, so
    /// before the fix both helpers came out `impl#[T]m().H#`. Read the pair: the two strings must differ,
    /// and each must be its own method's symbol plus `H#`.
    #[test]
    fn two_impls_whose_self_types_shorten_alike_keep_distinct_fn_local_items_a() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub mod a { pub struct T; }
    pub mod b { pub struct T; }
    impl crate::a::T {
       pub fn m() {
           use crate::a::T;
           struct H$0;
       }
    }
    impl crate::b::T {
       pub fn m() {
           use crate::b::T;
           struct H;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[`a::T`]m().H#",
        );
    }

    #[test]
    fn two_impls_whose_self_types_shorten_alike_keep_distinct_fn_local_items_b() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub mod a { pub struct T; }
    pub mod b { pub struct T; }
    impl crate::a::T {
       pub fn m() {
           use crate::a::T;
           struct H;
       }
    }
    impl crate::b::T {
       pub fn m() {
           use crate::b::T;
           struct H$0;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[`b::T`]m().H#",
        );
    }

    /// A trait impl carries the trait as well, again in the `SelfType` arm's order: `impl`, self type,
    /// trait. Two impls of two traits for ONE type would otherwise still collide.
    #[test]
    fn fn_local_item_under_a_trait_impl_names_the_trait() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct A;
    pub trait T { fn m(); }
    impl T for A {
       fn m() {
           struct Helper$0;
       }
    }
    "#,
            "rust-analyzer cargo main . impl#[A][T]m().Helper#",
        );
    }

    /// A trait's own default body is the other container the caller's walk cannot reach.
    #[test]
    fn fn_local_item_in_a_trait_default_body_is_qualified_by_the_trait() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub trait T {
       fn m() {
           struct Helper$0;
       }
    }
    "#,
            "rust-analyzer cargo main . T#m().Helper#",
        );
    }

    /// An enum variant's discriminant is a body whose owner is the VARIANT, and a variant is not an
    /// `ast::Item`, so the walk used to skip to the enum and produce `E#Helper#` -- the same string a
    /// type member `E::Helper` would get. Both the variant and the enum are named now.
    #[test]
    fn item_in_a_variant_discriminant_names_the_variant() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub enum E {
       A = { struct Helper$0; 0 },
    }
    "#,
            "rust-analyzer cargo main . E#A#Helper#",
        );
    }

    /// A block GENERATED BY A MACRO is in a macro file whose root is the expansion, so a plain
    /// `SyntaxNode::ancestors()` ended at that root, found no item and named nothing: the item came
    /// out as a bare `Helper#`, which collides with a module-level `Helper` and with the `Helper` of
    /// every other fn whose block came from a macro. Climbing out of the expansion reaches the macro
    /// call and, above it, the enclosing fn in the caller's file. This is the `select!` shape: the
    /// ITEM is written by the caller and passed in as an `$i:item` fragment, and only the BLOCK around
    /// it comes from the macro, so the block is still in the expansion.
    ///
    /// The item has to be the caller's. With the macro generating the item too
    /// (`($n:ident) => { { struct $n; } }`, cursor on `gen!(Helper)`) there is no reachable cursor:
    /// inside the macro body `check_symbol` gets no symbol ("must have one symbol None"), and on the
    /// argument neither `StaticIndex` nor `Analysis::moniker` resolves the token -- not even with the
    /// block and the fn removed from the fixture, so that is a limit of the instrument and not of this
    /// walk.
    #[test]
    fn item_in_a_macro_generated_block_is_qualified_by_the_enclosing_fn() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    macro_rules! wrap {
       ($i:item) => { { $i } };
    }
    pub fn func() {
       wrap! { struct Helper$0; }
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// PROBE for a DEFECT found on the tokio pack: 315 definition sites in 38 documents spell their owner
    /// TWICE (`actor_weak_sender().actor_weak_sender().MyActor#receiver.`). The shape there is
    /// `#[tokio::test] async fn f() { <item> }`, which expands to a non-async `fn f` whose body holds an
    /// `async` block holding the item -- a macro, an async block and a fn all at once. These three tests
    /// separate those causes; each asserts SINGLE naming, so whichever doubles is the one that fails.
    ///
    /// This one has no macro: a plain fn containing an `async` block containing the item.
    #[test]
    fn fn_local_item_in_an_async_block_names_its_fn_once() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       let _ = async { struct Helper$0; };
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// No macro and no block expression: the fn itself is `async`. If the doubling is here, the cause is
    /// that an async fn's body is reached through two block modules rather than one.
    #[test]
    fn fn_local_item_in_an_async_fn_names_its_fn_once() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub async fn func() {
       struct Helper$0;
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// A KNOWN RESIDUAL, found while writing fixtures for the doubled-owner defect and asserted here so
    /// that fixing it shows up as a failing test rather than as a silent change. An item inside an
    /// `async` block that a MACRO generates gets no owner at all -- the bare `Helper#` below is the
    /// pre-`31ebc2d` symbol, so it can collide with a module-level `Helper`.
    ///
    /// The `async` is the whole difference: `item_in_a_macro_generated_block_is_qualified_by_the_enclosing_fn`
    /// is this fixture with a plain `{ $i }` block and correctly gives `func().Helper#`, and
    /// `fn_local_item_in_an_async_block_names_its_fn_once` is this fixture without the macro and is also
    /// correct. Only the combination loses the owner, and the cause is not located yet.
    ///
    /// Its incidence on real code is UNMEASURED, and a pack cannot supply it: a symbol with no owner is
    /// indistinguishable from an item that really is at module level. That is the opposite of the
    /// doubled-owner defect, which a pack diff could count exactly because the wrong symbols were
    /// self-evidently wrong.
    #[test]
    fn fn_local_item_in_a_macro_generated_async_block_loses_its_owner() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    macro_rules! wrap {
       ($i:item) => { async { $i } };
    }
    pub fn func() {
       let _ = wrap! { struct Helper$0; };
    }
    "#,
            "rust-analyzer cargo main . Helper#",
        );
    }

    /// The tokio shape itself: an ATTRIBUTE macro over the fn, so the expansion contains a copy of the fn
    /// and the item sits in that copy's body. `#[tokio::test]` does this and also wraps the body in an
    /// `async` block; `identity` re-emits the item unchanged, which isolates the attribute from the async.
    #[test]
    fn fn_local_item_under_an_attribute_macro_names_its_fn_once() {
        check_symbol(
            r#"
    //- proc_macros: identity
    //- /workspace/lib.rs crate:main
    #[proc_macros::identity]
    fn func() {
       struct Helper$0;
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// The other half of the discriminating pair: the same attribute over an ASYNC fn. If the doubling
    /// appears here and not above, the async body is part of the cause; if it appears in both, the
    /// attribute alone is enough.
    #[test]
    fn fn_local_item_under_an_attribute_macro_on_an_async_fn_names_its_fn_once() {
        check_symbol(
            r#"
    //- proc_macros: identity
    //- /workspace/lib.rs crate:main
    #[proc_macros::identity]
    async fn func() {
       struct Helper$0;
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// The full tokio shape, assembled from a `macro_rules!` because the builtin fixture proc macros
    /// cannot rewrite a body: the expansion contains the FN, an `async` block inside it, and the caller's
    /// item inside that. `#[tokio::test] async fn f() { <item> }` expands to exactly this.
    #[test]
    fn fn_local_item_in_a_generated_fn_with_an_async_body_names_its_fn_once() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    macro_rules! tokio_test {
       ($n:ident, $($b:tt)*) => {
           fn $n() { let body = async { $($b)* }; }
       };
    }
    tokio_test!(func, struct Helper$0;);
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// Same shape with the generated fn's body holding the item directly, no async block, so the async is
    /// the only difference from the test above.
    #[test]
    fn fn_local_item_in_a_generated_fn_names_its_fn_once() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    macro_rules! plain_test {
       ($n:ident, $($b:tt)*) => {
           fn $n() { $($b)* }
       };
    }
    plain_test!(func, struct Helper$0;);
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// THE DEFECT, minimised from `tokio/benches/rt_multi_threaded.rs:105`, where
    /// `rt_multi_spawn_many_remote_busy2().rt_multi_spawn_many_remote_busy2().iter().` was emitted: 315
    /// definition sites in 38 tokio documents named their owner TWICE. It needs no macro and no `async` --
    /// only TWO NESTED BLOCK MODULES OVER ONE OWNER, which is what the `const` below buys. Without it the
    /// fn's body holds no item, so it is not a block module at all and the inner block's parent is the
    /// crate root (see `struct_in_a_bare_block_inside_a_fn_is_qualified_by_the_fn`); with it the chain is
    /// inner block -> fn body block -> crate root, the caller visits BOTH block modules, and each visit
    /// ran this walk from scratch and named `func` again.
    #[test]
    fn fn_local_item_in_a_nested_block_names_its_fn_once() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn func() {
       const C: u8 = 0;
       { struct Helper$0; }
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// THE SECOND ROUTE TO THE SAME DEFECT, which the `const` fixture above does not cover and which the
    /// write-up could only call untraced: the `#[tokio::test] async fn` sites (`tokio/tests/sync_mpsc_weak.rs`,
    /// 34 of the 326) reach two nested block modules through a STATEMENT MACRO instead of a `const`. A
    /// `m!();` statement expands to an item inside the body, and an item is all a `{ }` needs to become a
    /// block module -- exactly what `const C` buys above, with no `const` in the source. On the corpus it is
    /// `pin!`. Traced by rv-ra-symid in review round 3 and pinned here on their reproducer, so the route is
    /// named by a fixture and not only by the count that went to 0.
    #[test]
    fn fn_local_item_after_a_statement_macro_names_its_fn_once() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    macro_rules! m { () => {} }
    pub fn func() {
       m!();
       { struct Helper$0; }
    }
    "#,
            "rust-analyzer cargo main . func().Helper#",
        );
    }

    /// The other direction of the same fix, and the reason it dedupes by DEFINITION rather than by the
    /// rendered name: here the two owners are spelled identically and are two different functions, so the
    /// repetition is correct and must survive. A name-based guard would emit `f().S#` and put this item in
    /// the same symbol as an `S` in the outer `f`'s own body.
    #[test]
    fn fn_local_item_in_a_shadowing_fn_names_both_fns() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn f() {
       fn f() {
           struct S$0;
       }
    }
    "#,
            "rust-analyzer cargo main . f().f().S#",
        );
    }

    /// Both nesting levels of that shadowing pair, since asserting one alone would pass if the other
    /// collapsed onto it -- which is exactly what a name-based dedupe would do.
    #[test]
    fn fn_local_item_in_the_outer_of_two_shadowing_fns_is_distinct() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub fn f() {
       struct S$0;
       fn f() {
           struct S;
       }
    }
    "#,
            "rust-analyzer cargo main . f().S#",
        );
    }

    /// Two integration-test targets of ONE package, each defining `Data`. The symbol's package field
    /// is the package name for both and nothing else named the target, so both computed
    /// `... serde_test_suite 0.0.0 Data#`. On serde this class was 103 of 196 colliding symbols; the
    /// largest single member is `serde_test_suite 0.0.0 crate/`, the crate root of 21 integration-test
    /// targets under one name. (Rows of that report are grouped by class, so an exemplar has to be
    /// read with its heading: `Enum#`, 11 sites, is a FN-LOCAL collision, not this class.)
    ///
    /// Both halves are asserted, since pinning one alone passes when it equals the string it used to
    /// collide with.
    #[test]
    fn same_item_in_two_test_targets_of_one_package_is_distinct_a() {
        check_symbol(
            r#"
    //- /workspace/tests/test_de.rs crate:test_de package:serde_test_suite target:test
    struct Data$0;
    //- /workspace/tests/test_ser.rs crate:test_ser package:serde_test_suite target:test
    struct Data;
    "#,
            "rust-analyzer cargo serde_test_suite:test_de . Data#",
        );
    }

    #[test]
    fn same_item_in_two_test_targets_of_one_package_is_distinct_b() {
        check_symbol(
            r#"
    //- /workspace/tests/test_de.rs crate:test_de package:serde_test_suite target:test
    struct Data;
    //- /workspace/tests/test_ser.rs crate:test_ser package:serde_test_suite target:test
    struct Data$0;
    "#,
            "rust-analyzer cargo serde_test_suite:test_ser . Data#",
        );
    }

    /// `build.rs` is a target of the package too, so it is its own crate. Before this it shared the
    /// package's whole namespace with the lib target.
    #[test]
    fn build_script_target_is_distinct_from_the_lib_target() {
        check_symbol(
            r#"
    //- /workspace/build.rs crate:build_script_build package:mypkg target:build-script
    struct Shared$0;
    //- /workspace/src/lib.rs crate:mypkg package:mypkg target:lib
    struct Shared;
    "#,
            "rust-analyzer cargo mypkg:build_script_build . Shared#",
        );
    }

    /// CONTROL for this half: the package's LIBRARY target keeps exactly the symbol it had. This is
    /// the common case -- almost every symbol in a normal dependency -- so if it changed, the whole
    /// index would churn for nothing.
    #[test]
    fn lib_target_symbol_is_not_qualified() {
        check_symbol(
            r#"
    //- /workspace/src/lib.rs crate:mypkg package:mypkg target:lib
    pub mod m {
       pub struct Plain$0;
    }
    "#,
            "rust-analyzer cargo mypkg . m/Plain#",
        );
    }

    /// CONTROL: a lib target whose name differs from its package (`[lib] name = "..."`, or the
    /// `-`/`_` spelling of any hyphenated package) is still the lib, and must NOT be qualified. This
    /// is what makes the test a KIND question rather than a name comparison: comparing the crate name
    /// against the package name would qualify every symbol of every such package.
    #[test]
    fn renamed_lib_target_is_not_qualified() {
        check_symbol(
            r#"
    //- /workspace/src/lib.rs crate:serde_derive package:serde-derive target:lib
    pub struct Plain$0;
    "#,
            "rust-analyzer cargo serde-derive . Plain#",
        );
    }

    /// The other direction of the same point: a bin target named after its own package -- what
    /// `src/main.rs` gives you -- IS qualified, because the kind says it is not the lib. A name
    /// comparison could not see this case at all, and it is the common one for a binary crate.
    ///
    /// The lib half cannot be written into this fixture: `ChangeFixture` rejects two crates with the
    /// same name, and `foo`'s lib and bin are both named `foo`. `lib_target_symbol_is_not_qualified`
    /// is the other half -- the two expectations differ, which is the property being asserted.
    #[test]
    fn bin_target_named_after_its_package_is_qualified() {
        check_symbol(
            r#"
    //- /workspace/src/main.rs crate:foo package:foo target:bin
    pub struct Plain$0;
    "#,
            "rust-analyzer cargo foo:foo . Plain#",
        );
    }

    /// CONTROL for every project model that reports no cargo targets -- a JSON project, a detached
    /// file, most test fixtures. An unknown kind must read as "leave it alone", not as "not a lib":
    /// the other way round, every symbol of every such project would be qualified by its own crate
    /// name, which is churn with no collision to show for it.
    #[test]
    fn crate_with_no_known_target_kind_is_not_qualified() {
        check_symbol(
            r#"
    //- /workspace/src/lib.rs crate:mypkg package:mypkg
    pub struct Plain$0;
    "#,
            "rust-analyzer cargo mypkg . Plain#",
        );
    }

    /// A symbol must not depend on how the PRODUCER was configured. `cargo.allTargets` decides
    /// whether a package's test and bench targets are in the crate graph at all, and `scip.rs` is the
    /// one consumer that takes it from the user's `--config-path` (`config.cargo(None)`, where
    /// `analysis_stats`, `lsif`, `diagnostics` and `ssr` hardcode `true`). So a rule of the form "is
    /// this package's target count greater than one" would spell ripgrep's `main()` differently for
    /// two producers of the same commit.
    ///
    /// This pair is the testable substitute: the same bin crate alone, and beside a sibling test
    /// target of the same package, must give a byte-identical symbol. The step from `allTargets` to
    /// "a sibling crate is present in the graph" is NOT established here -- a `ChangeFixture` has no
    /// `CargoWorkspace` and cannot set the flag -- but by reading `cargo_workspace.rs` (where the flag
    /// is consumed) and `build_dependencies.rs`.
    #[test]
    fn bin_symbol_does_not_depend_on_a_sibling_test_target_a() {
        check_symbol(
            r#"
    //- /workspace/src/main.rs crate:rg package:ripgrep target:bin
    pub fn main$0() {}
    "#,
            "rust-analyzer cargo ripgrep:rg . main().",
        );
    }

    #[test]
    fn bin_symbol_does_not_depend_on_a_sibling_test_target_b() {
        check_symbol(
            r#"
    //- /workspace/src/main.rs crate:rg package:ripgrep target:bin
    pub fn main$0() {}
    //- /workspace/tests/integration.rs crate:integration package:ripgrep target:test
    fn t() {}
    "#,
            "rust-analyzer cargo ripgrep:rg . main().",
        );
    }

    /// The crate ROOT module of a non-lib target. The target is named in the package field, so the
    /// root keeps the `crate` descriptor it always had (and, as before, drops it when the symbol has
    /// other descriptors to carry).
    #[test]
    fn crate_root_of_a_non_lib_target_is_qualified_in_the_package_field() {
        check_symbol(
            r#"
    //- /workspace/tests/test_de.rs crate:test_de package:serde_test_suite target:test
    pub mod inner$0 {}
    "#,
            "rust-analyzer cargo serde_test_suite:test_de . inner/",
        );
    }

    /// A module named after a target is why the target goes in the package field and not into a
    /// descriptor: as a descriptor, `serde_test_suite . test_de/Data#` would be produced BOTH by
    /// `Data` in the test target `test_de` and by `Data` in a module `test_de` of the lib -- a new
    /// collision created by the fix for the old one. In the package field the two cannot meet.
    #[test]
    fn a_module_named_like_a_target_does_not_collide_with_it() {
        check_symbol(
            r#"
    //- /workspace/src/lib.rs crate:serde_test_suite package:serde_test_suite target:lib
    pub mod test_de {
       pub struct Data$0;
    }
    "#,
            "rust-analyzer cargo serde_test_suite . test_de/Data#",
        );
    }

    /// B1. One file can belong to several crates, and a `mod common;` pulled into two integration
    /// tests is exactly that. The crate a symbol is keyed to therefore cannot be "the crate of the
    /// module the walk happened to produce": the definition in `common.rs` is reached through the
    /// canonical owner of that file, while a reference from `tests/b.rs` is reached through crate
    /// `b`'s own tree, so the two would name different packages and would NOT JOIN. Unjoined is worse
    /// than collided: a collision at least links the sites together.
    ///
    /// The definition side and the reference-from-the-other-crate side assert the SAME string; that
    /// they are equal is the whole point, so both are spelled out rather than compared to a variable.
    #[test]
    fn a_file_shared_by_two_test_targets_keys_to_one_crate_def() {
        check_symbol(
            r#"
    //- /workspace/tests/a.rs crate:a package:p target:test
    mod common;
    //- /workspace/tests/b.rs crate:b package:p target:test
    mod common;
    //- /workspace/tests/common.rs
    pub fn helper$0() {}
    "#,
            "rust-analyzer cargo p:a . common/helper().",
        );
    }

    #[test]
    fn a_file_shared_by_two_test_targets_keys_to_one_crate_ref() {
        check_symbol(
            r#"
    //- /workspace/tests/a.rs crate:a package:p target:test
    mod common;
    //- /workspace/tests/b.rs crate:b package:p target:test
    mod common;
    fn use_it() { common::helper$0(); }
    //- /workspace/tests/common.rs
    pub fn helper() {}
    "#,
            "rust-analyzer cargo p:a . common/helper().",
        );
    }

    /// The MODULE of a shared file is the same case and needs its own pair, because a module's file
    /// and its parent's file can differ: here `common` lives in `tests/common.rs`, shared, while the
    /// `mod common;` that declares it is written once per test target. Keyed through the parent -- the
    /// module the definition sits IN, which is what every other definition is keyed through -- the
    /// declaration in `b.rs` named package `p:b` while the module's own document named `p:a`, so a
    /// module symbol did not join across targets. Measured on tokio before this: 11 unjoined module
    /// symbols, all of them `tests/support` files pulled into several integration tests, plus 3 on
    /// serde. Both arms assert the SAME string, which is the whole point of the pair.
    #[test]
    fn a_module_of_a_file_shared_by_two_test_targets_keys_to_one_crate_a() {
        check_symbol(
            r#"
    //- /workspace/tests/a.rs crate:a package:p target:test
    mod common$0;
    //- /workspace/tests/b.rs crate:b package:p target:test
    mod common;
    //- /workspace/tests/common.rs
    pub fn helper() {}
    "#,
            "rust-analyzer cargo p:a . common/",
        );
    }

    #[test]
    fn a_module_of_a_file_shared_by_two_test_targets_keys_to_one_crate_b() {
        check_symbol(
            r#"
    //- /workspace/tests/a.rs crate:a package:p target:test
    mod common;
    //- /workspace/tests/b.rs crate:b package:p target:test
    mod common$0;
    //- /workspace/tests/common.rs
    pub fn helper() {}
    "#,
            "rust-analyzer cargo p:a . common/",
        );
    }

    /// CONTROL. A module-level item must be completely unaffected: if this string changed, the
    /// descriptor change would be churning symbols it has no business touching, and the measured
    /// churn figure (serde 16.55% of definition sites) would be wrong in the other direction.
    /// That figure is from the corrected instrument. An earlier version of it said 16.59% with 92
    /// fn-local collisions; that version excluded a symbol's own site by identity rather than by
    /// span, so collisions landed in the wrong class, and 16.59% is retracted rather than merely
    /// superseded. Any figure of the same shape cited elsewhere has to be re-read from the current
    /// run, not carried across.
    #[test]
    fn module_level_item_symbol_is_unchanged() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub mod m {
       pub struct Plain$0;
       pub fn func() {}
    }
    "#,
            "rust-analyzer cargo main . m/Plain#",
        );
    }

    /// CONTROL, the other half: an item inside an `impl` inside a module is also untouched. The
    /// `impl` ancestor is deliberately skipped by the block walk, so an inherent method must keep
    /// the `impl#[Type]` shape it already had.
    #[test]
    fn inherent_method_symbol_is_unchanged() {
        check_symbol(
            r#"
    //- /workspace/lib.rs crate:main
    pub struct S;
    impl S {
       pub fn m$0(&self) {}
    }
    "#,
            "rust-analyzer cargo main . impl#[S]m().",
        );
    }

    #[test]
    fn documentation_matches_doc_comment() {
        let s = "/// foo\nfn bar() {}";

        let mut host = AnalysisHost::default();
        let change_fixture = ChangeFixture::parse(s);
        host.raw_database_mut().apply_change(change_fixture.change);

        let analysis = host.analysis();
        let si = StaticIndex::compute(
            &analysis,
            VendoredLibrariesConfig::Included {
                workspace_root: &VfsPath::new_virtual_path("/workspace".to_owned()),
            },
        );

        let file = si.files.first().unwrap();
        let (_, token_id) = file.tokens.get(1).unwrap(); // first token is file module, second is `bar`
        let token = si.tokens.get(*token_id).unwrap();

        assert_eq!(token.documentation.as_ref().map(|d| d.as_str()), Some("foo"));
    }

    #[test]
    fn function_has_enclosing_range() {
        let s = "fn foo() {}";

        let mut host = AnalysisHost::default();
        let change_fixture = ChangeFixture::parse(s);
        host.raw_database_mut().apply_change(change_fixture.change);

        let analysis = host.analysis();
        let si = StaticIndex::compute(
            &analysis,
            VendoredLibrariesConfig::Included {
                workspace_root: &VfsPath::new_virtual_path("/workspace".to_owned()),
            },
        );

        let file = si.files.first().unwrap();
        let (_, token_id) = file.tokens.get(1).unwrap(); // first token is file module, second is `foo`
        let token = si.tokens.get(*token_id).unwrap();

        let expected_range = FileRangeWrapper {
            file_id: FileId::from_raw(0),
            range: TextRange::new(0.into(), 11.into()),
        };

        assert_eq!(token.definition_body, Some(expected_range));
    }

    #[test]
    fn function_enclosing_range_trivia() {
        let s = "fn first() {}\n// belongs to first\n/// second docs\nfn second() {}";

        let mut host = AnalysisHost::default();
        let change_fixture = ChangeFixture::parse(s);
        host.raw_database_mut().apply_change(change_fixture.change);

        let analysis = host.analysis();
        let si = StaticIndex::compute(
            &analysis,
            VendoredLibrariesConfig::Included {
                workspace_root: &VfsPath::new_virtual_path("/workspace".to_owned()),
            },
        );

        let file = si.files.first().unwrap();
        let token = file
            .tokens
            .iter()
            .filter_map(|(_, token_id)| si.tokens.get(*token_id))
            .find(|token| token.display_name.as_deref() == Some("second"))
            .unwrap();

        let definition_body = token.definition_body.unwrap();
        assert_eq!(
            definition_body.range.start(),
            TextSize::new(s.find("/// second docs").unwrap() as u32)
        );
        assert_eq!(definition_body.range.end(), TextSize::of(s));
    }

    #[test]
    fn const_enclosing_range_trivia() {
        let s = "const FOO_ONE: i32 = 123; // one\nconst FOO_TWO: i32 = 123; // two";

        let mut host = AnalysisHost::default();
        let change_fixture = ChangeFixture::parse(s);
        host.raw_database_mut().apply_change(change_fixture.change);

        let analysis = host.analysis();
        let si = StaticIndex::compute(
            &analysis,
            VendoredLibrariesConfig::Included {
                workspace_root: &VfsPath::new_virtual_path("/workspace".to_owned()),
            },
        );

        let file = si.files.first().unwrap();
        let token = file
            .tokens
            .iter()
            .filter_map(|(_, token_id)| si.tokens.get(*token_id))
            .find(|token| token.display_name.as_deref() == Some("FOO_TWO"))
            .unwrap();

        let definition_body = token.definition_body.unwrap();
        assert_eq!(
            definition_body.range.start(),
            TextSize::new(s.find("const FOO_TWO").unwrap() as u32)
        );
        assert_eq!(definition_body.range.end(), TextSize::new(s.find(" // two").unwrap() as u32));
    }
}
