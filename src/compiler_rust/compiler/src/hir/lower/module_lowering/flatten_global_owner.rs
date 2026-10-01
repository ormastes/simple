//! Owner-qualified symbols for same-named module globals of a flattened unit.
//!
//! `pipeline::module_loader::load_module_with_imports` merges every imported
//! module into one item list, so two modules that each declare `var g_x`
//! reached HIR lowering under one bare name. Registration is last-write-wins,
//! so a function of the importer of `a.g_x` read `b.g_x` instead (measured:
//! `Cannot infer field type: struct 'BoxB' field 'a_field'`, a whole-module
//! JIT fallback to the interpreter). PR #1936 fixed the interpreter half; this
//! is the codegen half, mirroring the function-side `flatten_fn_owners` scheme.
//!
//! The flattener precedes every imported global declaration with a
//! `__simple_flatten_global_owner__=<owner>` marker const (entry-module
//! globals carry none, owner `None`). A name declared by two or more distinct
//! owners is a collision: every such declaration is renamed to
//! [`flattened_global_symbol`] on a clone of the module (only when a collision
//! exists, so collision-free units pay nothing), which makes every registry
//! keyed by the AST name -- `globals`, the `global_init_*` maps,
//! `dynamic_init_globals`, the module-init stores -- owner-exact at once.
//! References are resolved through the owner of the function being lowered by
//! `Lowerer::resolve_flatten_owned_global`.
//!
//! Units with no owner markers (native-project lane, single files) have every
//! owner `None`, so no name ever collides and this pass is a no-op there.

use std::collections::HashMap;

use simple_parser::ast::{Node, Pattern};
use simple_parser::Module;

use crate::interpreter::{flatten_owner_mangled_name, FLATTEN_GLOBAL_OWNER_MARKER_PREFIX};

/// Colliding global name -> owner of each declaration in item order.
pub(crate) type FlattenGlobalOwners = HashMap<String, Vec<Option<String>>>;

/// Prefix shared by every synthetic marker const the flattener emits.
const FLATTEN_MARKER_PREFIX: &str = "__simple_flatten_";

/// Symbol the global `name` declared by `owner` is lowered under.
///
/// Same policy as `Lowerer::flatten_emitted_symbol` for functions: the entry
/// module's declaration keeps the bare name when it has one, else the last
/// declaration does (exactly the one bare-name last-write-wins picked before),
/// so references nothing can attribute to an owner keep their old meaning.
/// Every other owner gets its owner-mangled symbol.
pub(crate) fn flattened_global_symbol(owners: &[Option<String>], owner: Option<&str>, name: &str) -> String {
    let Some(owner) = owner else {
        return name.to_string();
    };
    let entry_declares = owners.iter().any(Option::is_none);
    if !entry_declares && owners.last().and_then(|o| o.as_deref()) == Some(owner) {
        return name.to_string();
    }
    flatten_owner_mangled_name(owner, name)
}

fn global_decl_name(node: &Node) -> Option<&str> {
    let name = match node {
        Node::Let(l) => pattern_name(&l.pattern)?,
        Node::Const(c) => c.name.as_str(),
        Node::Static(s) => s.name.as_str(),
        _ => return None,
    };
    (!name.starts_with(FLATTEN_MARKER_PREFIX)).then_some(name)
}

fn pattern_name(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Identifier(n) | Pattern::MutIdentifier(n) | Pattern::MoveIdentifier(n) => Some(n.as_str()),
        Pattern::Typed { pattern, .. } => pattern_name(pattern),
        _ => None,
    }
}

fn rename_pattern(pattern: &mut Pattern, symbol: String) {
    match pattern {
        Pattern::Identifier(n) | Pattern::MutIdentifier(n) | Pattern::MoveIdentifier(n) => *n = symbol,
        Pattern::Typed { pattern, .. } => rename_pattern(pattern, symbol),
        _ => {}
    }
}

fn owner_marker(node: &Node) -> Option<&str> {
    match node {
        Node::Const(c) => c.name.strip_prefix(FLATTEN_GLOBAL_OWNER_MARKER_PREFIX),
        _ => None,
    }
}

/// Owner of each global declaration, in item order: the owner marker
/// immediately preceding it, or `None` (entry module / unflattened unit).
fn declaration_owners(items: &[Node]) -> Vec<(usize, &str, Option<String>)> {
    let mut out = Vec::new();
    let mut pending: Option<&str> = None;
    for (index, item) in items.iter().enumerate() {
        if let Some(owner) = owner_marker(item) {
            pending = Some(owner);
            continue;
        }
        if let Some(name) = global_decl_name(item) {
            out.push((index, name, pending.take().map(str::to_string)));
        } else {
            pending = None;
        }
    }
    out
}

/// Rename every colliding flattened global to its owner-exact symbol.
///
/// Returns `None` when no global name is declared by two distinct owners.
/// Otherwise returns the renamed module, the collision census (keyed by the
/// ORIGINAL name) and each renamed declaration's `symbol -> owner`.
pub(crate) fn module_with_owner_qualified_globals(
    ast_module: &Module,
) -> Option<(Module, FlattenGlobalOwners, HashMap<String, Option<String>>)> {
    let declarations = declaration_owners(&ast_module.items);
    let mut owners: FlattenGlobalOwners = HashMap::new();
    for (_, name, owner) in &declarations {
        owners.entry((*name).to_string()).or_default().push(owner.clone());
    }
    owners.retain(|_, list| list.iter().any(|owner| owner != &list[0]));
    if owners.is_empty() {
        return None;
    }

    let mut renames: Vec<(usize, String)> = Vec::new();
    let mut symbol_owners: HashMap<String, Option<String>> = HashMap::new();
    for (index, name, owner) in &declarations {
        let Some(list) = owners.get(*name) else {
            continue;
        };
        let symbol = flattened_global_symbol(list, owner.as_deref(), name);
        symbol_owners.insert(symbol.clone(), owner.clone());
        if symbol != *name {
            renames.push((*index, symbol));
        }
    }

    let mut module = ast_module.clone();
    for (index, symbol) in renames {
        match &mut module.items[index] {
            Node::Let(l) => rename_pattern(&mut l.pattern, symbol),
            Node::Const(c) => c.name = symbol,
            Node::Static(s) => s.name = symbol,
            _ => {}
        }
    }
    Some((module, owners, symbol_owners))
}
