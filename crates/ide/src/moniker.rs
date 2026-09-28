//! This module generates [moniker](https://microsoft.github.io/language-server-protocol/specifications/lsif/0.6.0/specification/#exportsImports)
//! for LSIF and LSP.

use core::fmt;

use hir::{Adt, AsAssocItem, Crate, HirDisplay, InFile, MacroKind, Semantics};
use ide_db::{
    FilePosition, RootDatabase,
    base_db::{CrateOrigin, LangCrateOrigin},
    defs::{Definition, IdentClass, NameClass},
    helpers::pick_best_token,
};
use itertools::Itertools;
use span::Edition;
use syntax::{AstNode, SyntaxKind::*, SyntaxNodePtr, T, ast, ast::HasName};

use crate::{RangeInfo, doc_links::token_as_doc_comment, parent_module::crates_for};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MonikerDescriptorKind {
    Namespace,
    Type,
    Term,
    Method,
    TypeParameter,
    Parameter,
    Macro,
    Meta,
}

// Subset of scip_types::SymbolInformation::Kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SymbolInformationKind {
    AssociatedType,
    Attribute,
    Constant,
    Enum,
    EnumMember,
    Field,
    Function,
    Macro,
    Method,
    Module,
    Parameter,
    SelfParameter,
    StaticMethod,
    StaticVariable,
    Struct,
    Trait,
    TraitMethod,
    Type,
    TypeAlias,
    TypeParameter,
    Union,
    Variable,
}

impl From<SymbolInformationKind> for MonikerDescriptorKind {
    fn from(value: SymbolInformationKind) -> Self {
        match value {
            SymbolInformationKind::AssociatedType => Self::Type,
            SymbolInformationKind::Attribute => Self::Meta,
            SymbolInformationKind::Constant => Self::Term,
            SymbolInformationKind::Enum => Self::Type,
            SymbolInformationKind::EnumMember => Self::Type,
            SymbolInformationKind::Field => Self::Term,
            SymbolInformationKind::Function => Self::Method,
            SymbolInformationKind::Macro => Self::Macro,
            SymbolInformationKind::Method => Self::Method,
            SymbolInformationKind::Module => Self::Namespace,
            SymbolInformationKind::Parameter => Self::Parameter,
            SymbolInformationKind::SelfParameter => Self::Parameter,
            SymbolInformationKind::StaticMethod => Self::Method,
            SymbolInformationKind::StaticVariable => Self::Term,
            SymbolInformationKind::Struct => Self::Type,
            SymbolInformationKind::Trait => Self::Type,
            SymbolInformationKind::TraitMethod => Self::Method,
            SymbolInformationKind::Type => Self::Type,
            SymbolInformationKind::TypeAlias => Self::Type,
            SymbolInformationKind::TypeParameter => Self::TypeParameter,
            SymbolInformationKind::Union => Self::Type,
            SymbolInformationKind::Variable => Self::Term,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MonikerDescriptor {
    pub name: String,
    pub desc: MonikerDescriptorKind,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MonikerIdentifier {
    pub crate_name: String,
    pub description: Vec<MonikerDescriptor>,
}

impl fmt::Display for MonikerIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.crate_name)?;
        f.write_fmt(format_args!("::{}", self.description.iter().map(|x| &x.name).join("::")))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MonikerKind {
    Import,
    Export,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MonikerResult {
    /// Uniquely identifies a definition.
    Moniker(Moniker),
    /// Specifies that the definition is a local, and so does not have a unique identifier. Provides
    /// a unique identifier for the container.
    Local { enclosing_moniker: Option<Moniker> },
}

impl MonikerResult {
    pub fn from_def(
        sema: &Semantics<'_, RootDatabase>,
        def: Definition<'_>,
        from_crate: Crate,
    ) -> Option<Self> {
        def_to_moniker(sema, def, from_crate)
    }
}

/// Information which uniquely identifies a definition which might be referenceable outside of the
/// source file. Visibility declarations do not affect presence.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Moniker {
    pub identifier: MonikerIdentifier,
    pub kind: MonikerKind,
    pub package_information: PackageInformation,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PackageInformation {
    pub name: String,
    pub repo: Option<String>,
    pub version: Option<String>,
    /// The cargo TARGET this definition's crate was built from, when that target is not the
    /// package's library: a bin, an integration test, a bench, an example, `build.rs`. `None` for a
    /// lib target and for every project model that does not report target kinds.
    ///
    /// This says WHICH target, not how to spell it. Each exporter decides that for itself: `scip`
    /// puts it in the symbol's package field, and the LSIF/LSP moniker does not use it at all, since
    /// a moniker is only compared against monikers from the same producer.
    pub target: Option<String>,
}

pub(crate) fn moniker(
    db: &RootDatabase,
    FilePosition { file_id, offset }: FilePosition,
) -> Option<RangeInfo<Vec<MonikerResult>>> {
    let sema = &Semantics::new(db);
    let file = sema.parse_guess_edition(file_id).syntax().clone();
    let current_crate: hir::Crate = crates_for(db, file_id).pop()?.into();
    let original_token = pick_best_token(file.token_at_offset(offset), |kind| match kind {
        IDENT
        | INT_NUMBER
        | LIFETIME_IDENT
        | T![self]
        | T![super]
        | T![crate]
        | T![Self]
        | COMMENT
        | INNER_DOC_COMMENT
        | OUTER_DOC_COMMENT => 2,
        kind if kind.is_trivia() => 0,
        _ => 1,
    })?;
    if let Some(doc_comment) = token_as_doc_comment(&original_token) {
        return doc_comment.get_definition_with_descend_at(sema, offset, |def, _, _| {
            let m = def_to_moniker(sema, def, current_crate)?;
            Some(RangeInfo::new(original_token.text_range(), vec![m]))
        });
    }
    let navs = sema
        .descend_into_macros_exact(original_token.clone())
        .into_iter()
        .filter_map(|token| {
            IdentClass::classify_token(sema, &token).map(IdentClass::definitions_no_ops).map(|it| {
                it.into_iter().flat_map(|def| def_to_moniker(sema, def, current_crate))
            })
        })
        .flatten()
        .unique()
        .collect::<Vec<_>>();
    Some(RangeInfo::new(original_token.text_range(), navs))
}

pub(crate) fn def_to_kind(db: &RootDatabase, def: Definition<'_>) -> SymbolInformationKind {
    use SymbolInformationKind::*;

    match def {
        Definition::Macro(it) => match it.kind(db) {
            MacroKind::Derive
            | MacroKind::DeriveBuiltIn
            | MacroKind::AttrBuiltIn
            | MacroKind::Attr => Attribute,
            MacroKind::Declarative | MacroKind::DeclarativeBuiltIn | MacroKind::ProcMacro => Macro,
        },
        Definition::Field(..) | Definition::TupleField(..) => Field,
        Definition::Module(..) | Definition::Crate(..) => Module,
        Definition::Function(it) => {
            if it.as_assoc_item(db).is_some() {
                if it.has_self_param(db) {
                    if it.has_body(db) { Method } else { TraitMethod }
                } else {
                    StaticMethod
                }
            } else {
                Function
            }
        }
        Definition::Adt(Adt::Struct(..)) => Struct,
        Definition::Adt(Adt::Union(..)) => Union,
        Definition::Adt(Adt::Enum(..)) => Enum,
        Definition::EnumVariant(..) => EnumMember,
        Definition::Const(..) => Constant,
        Definition::Static(..) => StaticVariable,
        Definition::Trait(..) => Trait,
        Definition::TypeAlias(it) => {
            if it.as_assoc_item(db).is_some() {
                AssociatedType
            } else {
                TypeAlias
            }
        }
        Definition::BuiltinType(..) => Type,
        Definition::BuiltinLifetime(_) => TypeParameter,
        Definition::SelfType(..) => TypeAlias,
        Definition::GenericParam(..) => TypeParameter,
        Definition::Local(it) => {
            if it.is_self(db) {
                SelfParameter
            } else if it.is_param(db) {
                Parameter
            } else {
                Variable
            }
        }
        Definition::Label(..) | Definition::InlineAsmOperand(_) => Variable, // For lack of a better variant
        Definition::DeriveHelper(..) => Attribute,
        Definition::BuiltinAttr(..) => Attribute,
        Definition::ToolModule(..) => Module,
        Definition::ExternCrateDecl(..) => Module,
        Definition::InlineAsmRegOrRegClass(..) => Module,
    }
}

/// Computes a `MonikerResult` for a definition. Result cases:
///
/// * `Some(MonikerResult::Moniker(_))` provides a unique `Moniker` which refers to a definition.
///
/// * `Some(MonikerResult::Local { .. })` provides a `Moniker` for the definition enclosing a local.
///
/// * `None` is returned for definitions which are not in a module: `BuiltinAttr`, `BuiltinType`,
///   `BuiltinLifetime`, `TupleField`, `ToolModule`, and `InlineAsmRegOrRegClass`. TODO: it might be
///   sensible to provide monikers that refer to some non-existent crate of compiler builtin
///   definitions.
pub(crate) fn def_to_moniker(
    sema: &Semantics<'_, RootDatabase>,
    definition: Definition<'_>,
    from_crate: Crate,
) -> Option<MonikerResult> {
    match definition {
        Definition::Local(_) | Definition::Label(_) | Definition::GenericParam(_) => {
            return Some(MonikerResult::Local {
                enclosing_moniker: enclosing_def_to_moniker(sema, definition, from_crate),
            });
        }
        _ => {}
    }
    Some(MonikerResult::Moniker(def_to_non_local_moniker(sema, definition, from_crate)?))
}

fn enclosing_def_to_moniker(
    sema: &Semantics<'_, RootDatabase>,
    mut def: Definition<'_>,
    from_crate: Crate,
) -> Option<Moniker> {
    loop {
        let enclosing_def = def.enclosing_definition(sema.db)?;
        if let Some(enclosing_moniker) = def_to_non_local_moniker(sema, enclosing_def, from_crate) {
            return Some(enclosing_moniker);
        }
        def = enclosing_def;
    }
}

fn def_to_non_local_moniker(
    sema: &Semantics<'_, RootDatabase>,
    definition: Definition<'_>,
    from_crate: Crate,
) -> Option<Moniker> {
    let db = sema.db;
    // For a MODULE the module is itself, not `definition.module(db)`, which is its parent. The two
    // differ where they are written in different files, and then keying on the parent breaks the join
    // this rule exists to make: `mod support { pub mod mpsc; }` is written once per integration test
    // with `tests/support/mpsc.rs` shared between them, so `support` lives in the test file -- one
    // per target -- while `mpsc` lives in the shared file. Keyed through the parent, the definition of
    // `mpsc` (reached through the canonical owner of the shared file) and a reference to it from
    // another target's test file named two different packages and did not join at all. Measured on
    // tokio: 11 such symbols, every one a module of a shared `tests/support` file, plus 3 on serde.
    let module = match definition {
        Definition::Module(module) => module,
        _ => definition.module(db)?,
    };
    let krate = defining_crate(sema, module);
    let edition = krate.edition(db);

    // Add descriptors for this definition and every enclosing definition.
    let mut reverse_description = vec![];
    let mut def = definition;
    loop {
        match def {
            Definition::SelfType(impl_) => {
                if let Some(trait_ref) = impl_.trait_ref(db) {
                    // Trait impls use the trait type for the 2nd parameter.
                    reverse_description.push(MonikerDescriptor {
                        name: display(db, module, trait_ref),
                        desc: MonikerDescriptorKind::TypeParameter,
                    });
                }
                // Both inherent and trait impls use the self type for the first parameter.
                reverse_description.push(MonikerDescriptor {
                    name: display(db, module, impl_.self_ty(db)),
                    desc: MonikerDescriptorKind::TypeParameter,
                });
                reverse_description.push(MonikerDescriptor {
                    name: "impl".to_owned(),
                    desc: MonikerDescriptorKind::Type,
                });
            }
            _ => {
                if let Some(name) = def.name(db) {
                    reverse_description.push(MonikerDescriptor {
                        name: name.display(db, edition).to_string(),
                        desc: def_to_kind(db, def).into(),
                    });
                } else {
                    match def {
                        Definition::Module(module) if module.is_crate_root(db) => {
                            // The cargo TARGET this crate was built from is NOT named here: it goes
                            // in `PackageInformation::target`, because a descriptor named after a
                            // target can collide with a module of the same name, while the package
                            // field cannot. See `non_lib_target_name`.
                            //
                            // only include `crate` namespace by itself because we prefer
                            // `rust-analyzer cargo foo . bar/` over `rust-analyzer cargo foo . crate/bar/`
                            if reverse_description.is_empty() {
                                reverse_description.push(MonikerDescriptor {
                                    name: "crate".to_owned(),
                                    desc: MonikerDescriptorKind::Namespace,
                                });
                            }
                        }
                        // The only other nameless module is a *block* module: the module introduced
                        // by a `{ ... }` that contains items, i.e. the body of a function, const or
                        // static. It contributed no descriptor at all, so an item defined inside a
                        // function body was named as though it sat at module level, and
                        // `fn a() { struct S; }` and `fn b() { struct S; }` in one module computed
                        // ONE symbol string for two distinct types.
                        //
                        // This arm is where the function has to name itself, and it is the only
                        // place it can: `Definition::enclosing_definition` maps a fn-local item to
                        // its block module, and the block module's `containing_module` skips the
                        // function outright, so the loop below never visits the function.
                        Definition::Module(module) => {
                            if !push_block_owner_descriptor(
                                sema,
                                module,
                                edition,
                                &mut reverse_description,
                            ) {
                                tracing::error!(
                                    ?def,
                                    "Encountered enclosing definition with no name"
                                );
                            }
                        }
                        _ => {
                            tracing::error!(?def, "Encountered enclosing definition with no name");
                        }
                    }
                }
            }
        }
        let Some(next_def) = def.enclosing_definition(db) else {
            break;
        };
        def = next_def;
    }
    if reverse_description.is_empty() {
        return None;
    }
    reverse_description.reverse();
    let description = reverse_description;

    Some(Moniker {
        identifier: MonikerIdentifier {
            crate_name: krate.display_name(db)?.crate_name().to_string(),
            description,
        },
        kind: if krate == from_crate { MonikerKind::Export } else { MonikerKind::Import },
        package_information: {
            let (name, repo, version) = match krate.origin(db) {
                CrateOrigin::Library { repo, name } => (name, repo, krate.version(db)),
                CrateOrigin::Local { repo, name } => (
                    name.unwrap_or(krate.display_name(db)?.canonical_name().to_owned()),
                    repo,
                    krate.version(db),
                ),
                CrateOrigin::Rustc { name } => (
                    name.clone(),
                    Some("https://github.com/rust-lang/rust/".to_owned()),
                    Some(format!("https://github.com/rust-lang/rust/compiler/{name}",)),
                ),
                CrateOrigin::Lang(lang) => (
                    krate.display_name(db)?.canonical_name().to_owned(),
                    Some("https://github.com/rust-lang/rust/".to_owned()),
                    Some(match lang {
                        LangCrateOrigin::Other => {
                            "https://github.com/rust-lang/rust/library/".into()
                        }
                        lang => format!("https://github.com/rust-lang/rust/library/{lang}",),
                    }),
                ),
            };
            PackageInformation {
                name: name.as_str().to_owned(),
                repo,
                version,
                target: non_lib_target_name(db, krate),
            }
        },
    })
}

/// The crate a definition's identity is keyed to: the crate whose module tree canonically owns the
/// FILE the definition is written in, which is not always the crate the walk that found it came from.
///
/// One file can belong to several crates, and a `mod common;` pulled into three integration tests is
/// exactly that -- three crates whose module trees each contain `tests/common.rs`. `Module::krate`
/// then answers with whichever tree produced this `Module`, so a definition in `common.rs` and a
/// reference to it from `tests/b.rs` would be keyed to DIFFERENT crates and their symbols would not
/// join at all. That is strictly worse than the collision the rest of this series removes: a
/// collision at least joins, and a consumer can see it.
///
/// The canonical owner is the first module `Semantics::file_to_module_def` reports for the file,
/// which is the same rule `static_index` uses to decide which module a document belongs to, so a
/// document's own symbol and the symbols of the items in it agree. The lookup is cached per file on
/// the `Semantics` (`SourceToDefCtx::file_to_def`), which is why this takes `sema` and not `db`: the
/// uncached route, `crate_def_map(db, krate).modules_for_file(..)`, is a linear scan of every module
/// of every crate in the source root, per definition.
///
/// RESIDUAL: "first" is in crate-graph order, so adding a target that also includes a shared file can
/// move that file's canonical owner and churn its symbols. Every rule that picks ONE owner has some
/// version of this, and a rule that does not pick one cannot join; recorded rather than fixed.
fn defining_crate(sema: &Semantics<'_, RootDatabase>, module: hir::Module) -> Crate {
    let db = sema.db;
    // For a block module this is the file the enclosing item is in, which is the file wanted here.
    // `_respecting_includes` because that is what `Semantics::hir_file_to_module_defs` uses, and an
    // `include!`d file has no module of its own to be canonical.
    let file_id = module.definition_source_file_id(db).original_file_respecting_includes(db);
    match sema.file_to_module_def(file_id.file_id(db)) {
        Some(canonical) => canonical.krate(db),
        // No module claims the file at all: keep the walk's own answer, which is the only one there
        // is. Deliberately not a `?`: failing to canonicalise must not drop the symbol.
        None => module.krate(db),
    }
}

/// The cargo target to qualify this crate's symbols with, or `None` to leave them exactly as they
/// were. `Some` iff the crate is a known target of its package that is NOT the package's library.
///
/// Every cargo target -- the lib, each bin, each integration test, each bench, each example,
/// `build.rs` -- is a separate crate, while the symbol's package field carries the PACKAGE name and
/// no other field of the symbol names the target. So two integration tests of one package that each
/// define `Data` computed ONE symbol string for two distinct types. On serde, 103 of 196 colliding
/// symbols have no definition site in any fn body and so can only be this or a real repeated module
/// path; the largest single member is `serde_test_suite 0.0.0 crate/`, the crate root of 21
/// integration-test targets under one name.
///
/// The question asked is the target's KIND, not whether its name differs from the package's. A name
/// comparison is both too weak and too strong: a package `foo` whose bin is also named `foo`, which
/// is what `src/main.rs` gives you, is name-identical to its lib and would stay collided, while a lib
/// target renamed away from its package (`[lib] name = ...`) would be qualified for no reason and
/// churn every symbol in the package's public API.
///
/// It is also NOT "does this package have more than one target". That count depends on
/// `cargo.allTargets`, which `scip.rs` alone takes from the user's `--config-path` (`config.cargo(None)`,
/// where `analysis_stats`/`lsif`/`diagnostics`/`ssr` hardcode `true`), so the same commit of the same
/// crate would get different symbols from two producers: ripgrep is bin-only with `allTargets` false
/// and bin + test targets with it true.
fn non_lib_target_name(db: &RootDatabase, krate: Crate) -> Option<String> {
    match krate.target_kind(db) {
        Some(kind) if !kind.is_lib_like() => {}
        // Not a cargo project, or a kind this does not model: leave the symbols alone. A missing
        // kind must not read as "not a lib", or every JSON-project and detached-file symbol would be
        // qualified by its own crate name.
        Some(_) | None => return None,
    }
    // The TARGET name, which is what `add_target_crate_root` puts in the display name (`CrateOrigin`
    // carries the package name instead). `canonical_name` rather than `crate_name`, because this is
    // spelled into the package field where cargo's own spelling belongs: a target declared as
    // `foo-bar` is `foo-bar` to cargo, though its crate name is `foo_bar`.
    Some(krate.display_name(db)?.canonical_name().to_string())
}

/// If `module` is a block module, push descriptors naming the item that OWNS the body the block sits
/// in, and the `impl` or `trait` that item is an associated item of, so an item defined inside a
/// function body carries that function -- and that function's impl -- in its identity. Returns
/// whether `module` was a block module at all; `false` means the caller's own diagnostic still
/// applies. Returning `true` having pushed nothing is normal and is not a failure: see `const _`
/// below.
///
/// The WALK is syntactic on purpose. There is no hir route from a block module to the item that owns
/// its body -- `ModuleId::containing_module` does not go there and there is no `owning_definition` --
/// but a block module's definition source IS the `BlockExpr`. Every NAME, however, is resolved
/// through hir (`NameClass::classify`) and spelled with `Name::display(db, edition)`, the same
/// renderer and the same kind mapping the caller uses for a definition's own name: the syntax token
/// differs from it for a raw identifier (`r#foo`), so naming an owner from syntax spelled the same
/// function two ways in one symbol string.
///
/// Ancestors are walked with `Semantics::ancestors_with_macros_file`, which climbs OUT of a macro
/// expansion. A `select!`-style macro that expands to items inside a block has those items in a macro
/// file whose root is the expansion, so a plain `SyntaxNode::ancestors()` ended there and named
/// nothing at all.
///
/// WHICH ancestors, and where to stop, follows from what the caller's loop reaches on its own.
/// `BlockId` records the module passed to the body lowerer, which is the module the body's OWNER
/// lives in, and it is the same for every block in one body (`expr_store::lower::collect_block_`).
/// So:
///
///   * the caller's loop DOES walk item nesting: from `fn outer() { fn inner() { .. } }`, `inner`'s
///     body block leads to `outer`'s body block, which names `outer`. Walking every ancestor here as
///     well produced `outer().outer().inner().S#`.
///   * the caller's loop does NOT walk block nesting: from `fn func() { { struct Helper; } }`, the
///     bare block leads straight to the crate root, skipping `func`'s body block. Taking only the
///     block's immediate parent here produced a bare `Helper#`, with no `func()` at all -- worse
///     than before the change, since it can now collide with a module-level `Helper`.
///   * the caller's loop never reaches the `impl` or `trait` an associated item belongs to: a block
///     module's `parent` is the module the impl lives in, so `impl A { fn m() { struct H; } }` and
///     `impl B { fn m() { struct H; } }` both computed `m().H#`. That is why the walk does not stop
///     at the body owner: it continues to name an enclosing `impl` or `trait`, and only then stops.
///
/// The first two were observed, not predicted. Stopping at the SECOND body owner is what satisfies
/// them together with the third: the second owner is exactly the one the caller's own loop reaches.
fn push_block_owner_descriptor(
    sema: &Semantics<'_, RootDatabase>,
    module: hir::Module,
    edition: Edition,
    reverse_description: &mut Vec<MonikerDescriptor>,
) -> bool {
    let db = sema.db;
    let source = module.definition_source(db);
    let hir::ModuleSource::BlockExpr(block) = &source.value else {
        return false;
    };
    // `definition_source` reads the tree through `db`, which this `Semantics` has never seen, and
    // `to_def` on a node of an unknown tree panics rather than returning `None`. `to_node_syntax`
    // re-roots the block in the tree `sema` owns and registers the file, in one cached step.
    let block = sema.to_node_syntax(InFile::new(source.file_id, SyntaxNodePtr::new(block.syntax())));

    let mut named_body_owner = false;
    let mut pushed = 0usize;
    for node in sema.ancestors_with_macros_file(InFile::new(source.file_id, block)).skip(1) {
        let node = node.value;
        // An enum variant is not an `ast::Item`, so the walk used to skip past it to the enum and
        // `enum E { A = { struct H; 0 } }` named `H` as `E#H#` -- which is what a type member `E::H`
        // is called. The discriminant's body owner IS the variant, so name it and keep going: the
        // enum above it is not reached by the caller either.
        if let Some(variant) = ast::Variant::cast(node.clone()) {
            named_body_owner = true;
            push_owner_descriptor(sema, edition, variant.name(), reverse_description, &mut pushed);
            continue;
        }
        let Some(item) = ast::Item::cast(node) else { continue };
        let name = match &item {
            // The item kinds that own a body. Whichever comes first owns this block; a SECOND one
            // encloses that owner and the caller's loop reaches it through the chain of block
            // modules, so stop rather than name it twice.
            //
            // `const _: () = { .. }` -- the shape derive macros emit -- has an `_` token where the
            // name goes, so there is no name to resolve and the items inside it stay ambiguous.
            // Deliberate: the only alternative is a positional index, which is not stable across
            // edits, so inserting one `const _` above another would churn every symbol below it.
            // Traced as a residual rather than passed over in silence.
            ast::Item::Fn(it) => it.name(),
            ast::Item::Const(it) => it.name(),
            ast::Item::Static(it) => it.name(),
            // A type alias can be an associated item, so the walk continues past it like the three
            // above. Reached by a block in a type position, e.g. an array length.
            ast::Item::TypeAlias(it) => it.name(),
            // Also reached from a type position, but none of these can be an associated item, so
            // nothing above one belongs in this descriptor: name it and stop.
            ast::Item::Struct(it) => {
                push_owner_descriptor(sema, edition, it.name(), reverse_description, &mut pushed);
                break;
            }
            ast::Item::Enum(it) => {
                push_owner_descriptor(sema, edition, it.name(), reverse_description, &mut pushed);
                break;
            }
            ast::Item::Union(it) => {
                push_owner_descriptor(sema, edition, it.name(), reverse_description, &mut pushed);
                break;
            }
            // The two containers of associated items. Naming one is the last thing this walk does:
            // above a `trait` or `impl` there is only a module the caller reaches itself.
            ast::Item::Trait(it) => {
                push_owner_descriptor(sema, edition, it.name(), reverse_description, &mut pushed);
                break;
            }
            ast::Item::Impl(it) => {
                // An impl has no name. Spelled exactly as the `Definition::SelfType` arm above
                // spells it -- same renderer, same order, same descriptor kinds -- so that a
                // fn-local item under an impl and the impl's own symbol agree on the impl.
                match sema.to_def(it) {
                    Some(impl_) => {
                        if let Some(trait_ref) = impl_.trait_ref(db) {
                            reverse_description.push(MonikerDescriptor {
                                name: display(db, module, trait_ref),
                                desc: MonikerDescriptorKind::TypeParameter,
                            });
                        }
                        reverse_description.push(MonikerDescriptor {
                            name: display(db, module, impl_.self_ty(db)),
                            desc: MonikerDescriptorKind::TypeParameter,
                        });
                        reverse_description.push(MonikerDescriptor {
                            name: "impl".to_owned(),
                            desc: MonikerDescriptorKind::Type,
                        });
                        pushed += 1;
                    }
                    None => tracing::debug!("block owner impl did not resolve"),
                }
                break;
            }
            // A `macro_rules!`, a `use`, an extern block: nothing to contribute, and the walk must
            // still STOP, because going past one would name an item the caller reaches on its own.
            _ => break,
        };
        if named_body_owner {
            break;
        }
        named_body_owner = true;
        push_owner_descriptor(sema, edition, name, reverse_description, &mut pushed);
    }
    if pushed == 0 {
        // The residual this leaves: an item under an unnameable owner keeps the identity it had
        // before this walk existed, i.e. it is still ambiguous with its siblings.
        tracing::debug!("block module contributed no owner descriptor");
    }
    true
}

/// Pushes one descriptor for the owner `name` belongs to, resolved through hir so that it is spelled
/// the way every other consumer of `ide_db` spells it -- including the proc-macro case, where the
/// `Definition` for a `fn` is a `Macro`, and the raw-identifier case, where the syntax token `r#foo`
/// is not what `Name::display` produces.
///
/// `pushed` counts the descriptors that actually landed. Each way of failing to name an owner is a
/// SILENT residual -- the items under that owner keep the ambiguous identity they had before this
/// walk existed -- so each is traced with its own reason rather than being passed over.
fn push_owner_descriptor(
    sema: &Semantics<'_, RootDatabase>,
    edition: Edition,
    name: Option<ast::Name>,
    reverse_description: &mut Vec<MonikerDescriptor>,
    pushed: &mut usize,
) {
    let db = sema.db;
    let Some(name) = name else {
        // `const _: () = { .. }`, `impl` -- no name token to resolve from.
        tracing::debug!("block owner has no name token");
        return;
    };
    let Some(def) = NameClass::classify(sema, &name).and_then(NameClass::defined) else {
        tracing::debug!("block owner did not resolve to a definition");
        return;
    };
    let Some(name) = def.name(db) else {
        tracing::debug!(?def, "block owner definition has no name");
        return;
    };
    reverse_description.push(MonikerDescriptor {
        name: name.display(db, edition).to_string(),
        desc: def_to_kind(db, def).into(),
    });
    *pushed += 1;
}

fn display<'db, T: HirDisplay<'db>>(db: &'db RootDatabase, module: hir::Module, it: T) -> String {
    match it.display_source_code(db, module.into(), true) {
        Ok(result) => result,
        // Fallback on display variant that always succeeds
        Err(_) => {
            let fallback_result =
                it.display(db, module.krate(db).to_display_target(db)).to_string();
            tracing::error!(
                display = %fallback_result, "`display_source_code` failed; falling back to using display"
            );
            fallback_result
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{MonikerResult, fixture};

    use super::MonikerKind;

    #[allow(dead_code)]
    #[track_caller]
    fn no_moniker(#[rust_analyzer::rust_fixture] ra_fixture: &str) {
        let (analysis, position) = fixture::position(ra_fixture);
        if let Some(x) = analysis.moniker(position).unwrap() {
            assert_eq!(x.info.len(), 0, "Moniker found but no moniker expected: {x:?}");
        }
    }

    #[track_caller]
    fn check_local_moniker(
        #[rust_analyzer::rust_fixture] ra_fixture: &str,
        identifier: &str,
        package: &str,
        kind: MonikerKind,
    ) {
        let (analysis, position) = fixture::position(ra_fixture);
        let x = analysis.moniker(position).unwrap().expect("no moniker found").info;
        assert_eq!(x.len(), 1);
        match x.into_iter().next().unwrap() {
            MonikerResult::Local { enclosing_moniker: Some(x) } => {
                assert_eq!(identifier, x.identifier.to_string());
                assert_eq!(package, format!("{:?}", x.package_information));
                assert_eq!(kind, x.kind);
            }
            MonikerResult::Local { enclosing_moniker: None } => {
                panic!("Unexpected local with no enclosing moniker");
            }
            MonikerResult::Moniker(_) => {
                panic!("Unexpected non-local moniker");
            }
        }
    }

    #[track_caller]
    fn check_moniker(
        #[rust_analyzer::rust_fixture] ra_fixture: &str,
        identifier: &str,
        package: &str,
        kind: MonikerKind,
    ) {
        let (analysis, position) = fixture::position(ra_fixture);
        let x = analysis.moniker(position).unwrap().expect("no moniker found").info;
        assert_eq!(x.len(), 1);
        match x.into_iter().next().unwrap() {
            MonikerResult::Local { enclosing_moniker } => {
                panic!("Unexpected local enclosed in {enclosing_moniker:?}");
            }
            MonikerResult::Moniker(x) => {
                assert_eq!(identifier, x.identifier.to_string());
                assert_eq!(package, format!("{:?}", x.package_information));
                assert_eq!(kind, x.kind);
            }
        }
    }

    #[test]
    fn basic() {
        check_moniker(
            r#"
//- /lib.rs crate:main deps:foo
use foo::module::func;
fn main() {
    func$0();
}
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod module {
    pub fn func() {}
}
"#,
            "foo::module::func",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Import,
        );
        check_moniker(
            r#"
//- /lib.rs crate:main deps:foo
use foo::module::func;
fn main() {
    func();
}
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod module {
    pub fn func$0() {}
}
"#,
            "foo::module::func",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn moniker_for_trait() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod module {
    pub trait MyTrait {
        pub fn func$0() {}
    }
}
"#,
            "foo::module::MyTrait::func",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn moniker_for_trait_constant() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod module {
    pub trait MyTrait {
        const MY_CONST$0: u8;
    }
}
"#,
            "foo::module::MyTrait::MY_CONST",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn moniker_for_trait_type() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod module {
    pub trait MyTrait {
        type MyType$0;
    }
}
"#,
            "foo::module::MyTrait::MyType",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn moniker_for_trait_impl_function() {
        check_moniker(
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
            "foo::module::impl::MyStruct::MyTrait::func",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn moniker_for_field() {
        check_moniker(
            r#"
//- /lib.rs crate:main deps:foo
use foo::St;
fn main() {
    let x = St { a$0: 2 };
}
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub struct St {
    pub a: i32,
}
"#,
            "foo::St::a",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Import,
        );
    }

    /// A block GENERATED BY A MACRO lives in a macro file whose root is the expansion, so a plain
    /// `SyntaxNode::ancestors()` walk ended at that root, found no enclosing item and named nothing:
    /// the struct came out as `foo::Helper`, colliding with a `Helper` at the module level and with
    /// the `Helper` of any other fn whose block came from a macro. Climbing out of the expansion
    /// reaches the macro call and, above it, `fn func` in the caller's file. This is the `select!`
    /// shape: the ITEM is written by the caller and passed in as a fragment, and only the BLOCK
    /// around it comes from the macro.
    ///
    /// The variant where the macro generates the item too (`($n:ident) => { { struct $n; } }`, cursor
    /// on the `Helper` of `gen!(Helper)`) cannot be tested through this API at all: it returns no
    /// moniker for that cursor even with no block and no fn anywhere in the fixture
    /// (`macro_rules! gen { ($n:ident) => { struct $n; }; } gen!(Helper);` -> zero definitions), so a
    /// test of that shape would assert against the instrument rather than against this walk.
    #[test]
    fn block_from_a_macro_expansion_is_named_by_the_enclosing_fn() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
macro_rules! wrap {
    ($i:item) => { { $i } };
}
pub fn func() {
    wrap! { struct Helper$0; }
}
"#,
            "foo::func::Helper",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    /// An extern block is not a namespace, so it contributes no descriptor -- but it must not stop
    /// the walk either. `Definition::enclosing_definition` used to return `None` for an extern
    /// block's container, which truncated the walk at the item itself, so this identifier was `f`
    /// with no module path and no crate root reached.
    #[test]
    fn extern_block_item_keeps_its_module_path() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod ffi {
    unsafe extern "C" {
        pub fn f$0();
    }
}
"#,
            "foo::ffi::f",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    /// The consequence of the truncation, in the form that matters to a consumer: without the module
    /// path, these two distinct functions computed ONE identifier. The two expectations below differ
    /// only in the module, which is the whole point -- read them as a pair.
    #[test]
    fn two_extern_fns_of_one_name_in_two_modules_differ_a() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod a {
    unsafe extern "C" {
        pub fn f$0();
    }
}
pub mod b {
    unsafe extern "C" {
        pub fn f();
    }
}
"#,
            "foo::a::f",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn two_extern_fns_of_one_name_in_two_modules_differ_b() {
        check_moniker(
            r#"
//- /foo/lib.rs crate:foo@0.1.0,https://a.b/foo.git library
pub mod a {
    unsafe extern "C" {
        pub fn f();
    }
}
pub mod b {
    unsafe extern "C" {
        pub fn f$0();
    }
}
"#,
            "foo::b::f",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }

    /// A non-lib target reports WHICH target it is, and the identifier does not change: a moniker is
    /// only ever compared against monikers from the same producer, so the LSIF/LSP side has no
    /// collision to fix, and spelling the target into the identifier would churn it for nothing.
    /// `scip` is what reads this field.
    #[test]
    fn non_lib_target_is_reported_in_the_package_information() {
        check_moniker(
            r#"
//- /workspace/tests/test_de.rs crate:test_de package:serde_test_suite target:test
pub struct Data$0;
"#,
            "test_de::Data",
            r#"PackageInformation { name: "serde_test_suite", repo: None, version: None, target: Some("test_de") }"#,
            MonikerKind::Export,
        );
    }

    /// CONTROL: the package's lib target reports no target at all, so its symbols are untouched.
    #[test]
    fn lib_target_reports_no_target() {
        check_moniker(
            r#"
//- /workspace/src/lib.rs crate:mypkg package:mypkg target:lib
pub struct Data$0;
"#,
            "mypkg::Data",
            r#"PackageInformation { name: "mypkg", repo: None, version: None, target: None }"#,
            MonikerKind::Export,
        );
    }

    #[test]
    fn local() {
        check_local_moniker(
            r#"
//- /lib.rs crate:main deps:foo
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
            "foo::module::func",
            r#"PackageInformation { name: "foo", repo: Some("https://a.b/foo.git"), version: Some("0.1.0"), target: None }"#,
            MonikerKind::Export,
        );
    }
}
