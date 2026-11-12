//! Owner-qualified identity for same-named structs/classes of a flattened unit.
//!
//! `pipeline::module_loader::load_module_with_imports` merges every imported
//! module into one item list, so two modules that each declare
//! `struct TextSpan` with DIFFERENT fields reached HIR lowering under one bare
//! name. The type registry is keyed by that name, so one layout won and every
//! function of the other module failed with `Cannot infer field type: struct
//! 'TextSpan' field 'end'` -- a whole-program JIT fallback to the interpreter
//! (measured on `src/app/cli/native_build_main.spl`:
//! `10.frontend/block_types.TextSpan {start, end}` vs
//! `db/accel.TextSpan {value, start, len}`).
//!
//! This is the type twin of `flatten_global_owner.rs` (globals) and the
//! `flatten_fn_owners` scheme (functions):
//!
//! * Census: a struct/class name declared by two or more distinct owners with
//!   differing field layouts (names or types) is a collision. Identical layouts are left alone
//!   (bare-name sharing is already correct for them).
//! * Declarations: on a clone of the module (only when a collision exists),
//!   each colliding declaration is renamed to [`flattened_global_symbol`] --
//!   the entry module's (or else the last) declaration keeps the bare name, so
//!   references nothing can attribute keep their historical meaning. Because
//!   the declaration itself is renamed, every name-keyed registry downstream
//!   (type registry, `Name.method` symbols, method return types, impls) is
//!   owner-exact at once.
//! * Declaration signatures (fn params/returns, struct/class field types, impl
//!   targets, typed module globals) are rewritten on the same clone through the
//!   declaring owner's scope.
//! * Bodies: `Lowerer::enter_flatten_struct_scope` installs the current
//!   function owner's scope as a type-registry overlay, so every bare-name
//!   `types.lookup` inside the body (annotations, constructors, static calls,
//!   patterns) resolves owner-exactly.
//!
//! Scope of a name `N` seen from owner `O`: `O`'s own declaration of `N`, else
//! the declaration named by `O`'s selective import of `N` (aliases and
//! re-export chains followed through the flattener's import-binding markers),
//! else the declaration exactly one of `O`'s glob sources (`use m.*`, bare
//! `use m`) reaches, else unchanged (bare).
//!
//! Units with no owner attributes (native-project lane, single files) have
//! every owner `None`, so no name ever collides and this pass is a no-op.
//! The interpreter never sees the clone.

use std::collections::HashMap;

use simple_parser::ast::{Node, Type};
use simple_parser::Module;

use super::flattened_global_symbol;
use crate::hir::lower::lowerer::Lowerer;
use crate::interpreter::FLATTEN_GLOBAL_OWNER_MARKER_PREFIX;

/// Colliding struct/class name -> owner of each declaration in item order.
pub(crate) type FlattenStructOwners = HashMap<String, Vec<Option<String>>>;

/// Importer owner key -> local name -> (source owner, source name).
pub(crate) type FlattenImportBindings = HashMap<String, HashMap<String, (String, String)>>;

/// Bare name -> owner-exact symbol, as seen from one owner.
pub(crate) type FlattenStructScope = HashMap<String, String>;

/// Upper bound on re-export hops followed for one name (cycle guard).
const MAX_REEXPORT_HOPS: usize = 32;

fn declaration_owner(
    attributes: &[simple_parser::ast::Attribute],
    methods: &[simple_parser::ast::FunctionDef],
) -> Option<String> {
    Lowerer::flatten_owner_of(attributes.iter().map(|a| a.name.as_str())).or_else(|| {
        Lowerer::flatten_owner_of(
            methods
                .iter()
                .flat_map(|m| m.attributes.iter().map(|a| a.name.as_str())),
        )
    })
}

/// Layout of a nominal declaration: struct/class fields, or enum variants
/// with their payload (field name, type) lists.
type Layout<'a> = Vec<(&'a str, Vec<(Option<&'a str>, &'a Type)>)>;

/// `(name, owner, layout)` of a struct/class/enum declaration.
fn struct_declaration(node: &Node) -> Option<(&str, Option<String>, Layout<'_>)> {
    match node {
        Node::Struct(s) => Some((
            s.name.as_str(),
            declaration_owner(&s.attributes, &s.methods),
            s.fields.iter().map(|f| (f.name.as_str(), vec![(None, &f.ty)])).collect(),
        )),
        Node::Class(c) => Some((
            c.name.as_str(),
            declaration_owner(&c.attributes, &c.methods),
            c.fields.iter().map(|f| (f.name.as_str(), vec![(None, &f.ty)])).collect(),
        )),
        // Same-named enums with different variant sets collide exactly like
        // structs with different fields: the registry is keyed by bare name,
        // so the last registration's variants won and every `E.Variant` of the
        // other module failed MIR lowering ("unknown variant or method").
        Node::Enum(e) => Some((
            e.name.as_str(),
            declaration_owner(&e.attributes, &e.methods),
            e.variants
                .iter()
                .map(|v| {
                    let payload = v.fields.iter().flatten().map(|f| (f.name.as_deref(), &f.ty)).collect();
                    (v.name.as_str(), payload)
                })
                .collect(),
        )),
        _ => None,
    }
}

fn census(items: &[Node]) -> FlattenStructOwners {
    let mut owners: FlattenStructOwners = HashMap::new();
    let mut layouts: HashMap<&str, Vec<Layout<'_>>> = HashMap::new();
    for item in items {
        if let Some((name, owner, fields)) = struct_declaration(item) {
            owners.entry(name.to_string()).or_default().push(owner);
            layouts.entry(name).or_default().push(fields);
        }
    }
    owners.retain(|name, list| {
        let distinct_owners = list.iter().any(|owner| owner != &list[0]);
        let layouts = &layouts[name.as_str()];
        let distinct_layouts = layouts.iter().any(|layout| layout != &layouts[0]);
        distinct_owners && distinct_layouts
    });
    owners
}

/// Importer owner key -> modules it glob-imports (`use m.*`, bare `use m`).
pub(crate) type FlattenGlobSources = HashMap<String, Vec<String>>;

/// Owner-exact symbol of the colliding declaration `name` reachable from
/// module `owner`: its own declaration, else the one its selective import of
/// the name designates, else the one exactly ONE of its glob sources reaches
/// (two distinct glob candidates are ambiguous -> `None`, bare meaning kept).
fn resolve_through(
    owners: &FlattenStructOwners,
    bindings: &FlattenImportBindings,
    globs: &FlattenGlobSources,
    owner: &str,
    name: &str,
    hops: usize,
    seen: &mut std::collections::HashSet<(String, String)>,
) -> Option<String> {
    // Each (module, name) is visited once: bounds the glob walk and breaks
    // import cycles.
    if hops > MAX_REEXPORT_HOPS || !seen.insert((owner.to_string(), name.to_string())) {
        return None;
    }
    if let Some(list) = owners.get(name) {
        if list.iter().any(|declared| declared.as_deref() == Some(owner)) {
            return Some(flattened_global_symbol(list, Some(owner), name));
        }
    }
    if let Some((source_owner, source_name)) = bindings.get(owner).and_then(|imports| imports.get(name)) {
        // Selective import (or re-export facade): follow the source module.
        return resolve_through(owners, bindings, globs, source_owner, source_name, hops + 1, seen);
    }
    let mut found: Option<String> = None;
    for glob_owner in globs.get(owner).into_iter().flatten() {
        if glob_owner == owner {
            continue;
        }
        if let Some(symbol) = resolve_through(owners, bindings, globs, glob_owner, name, hops + 1, seen) {
            match &found {
                Some(previous) if previous != &symbol => return None,
                _ => found = Some(symbol),
            }
        }
    }
    found
}

/// Owner-exact symbol of the struct/class/enum `name` as seen from `current`,
/// or `None` when nothing attributes it (keep the bare-name lookup).
pub(crate) fn resolve_owned_struct(
    owners: &FlattenStructOwners,
    bindings: &FlattenImportBindings,
    globs: &FlattenGlobSources,
    current: Option<&str>,
    name: &str,
) -> Option<String> {
    if let Some(list) = owners.get(name) {
        if list.iter().any(|owner| owner.as_deref() == current) {
            return Some(flattened_global_symbol(list, current, name));
        }
    }
    let mut seen = std::collections::HashSet::new();
    resolve_through(owners, bindings, globs, current.unwrap_or("<entry>"), name, 0, &mut seen)
}

/// Every bare (or aliased) name whose meaning from `current` differs from the
/// plain registry entry.
pub(crate) fn struct_scope_for(
    owners: &FlattenStructOwners,
    bindings: &FlattenImportBindings,
    globs: &FlattenGlobSources,
    current: Option<&str>,
) -> FlattenStructScope {
    let mut scope = FlattenStructScope::new();
    for name in owners.keys() {
        if let Some(symbol) = resolve_owned_struct(owners, bindings, globs, current, name) {
            if &symbol != name {
                scope.insert(name.clone(), symbol);
            }
        }
    }
    if let Some(imports) = bindings.get(current.unwrap_or("<entry>")) {
        for local in imports.keys() {
            if scope.contains_key(local) || owners.contains_key(local) {
                continue;
            }
            if let Some(symbol) = resolve_owned_struct(owners, bindings, globs, current, local) {
                if &symbol != local {
                    scope.insert(local.clone(), symbol);
                }
            }
        }
    }
    scope
}

fn rewrite_name(name: &mut String, scope: &FlattenStructScope) {
    if let Some(symbol) = scope.get(name.as_str()) {
        *name = symbol.clone();
    } else if let Some(symbol) = name.strip_suffix('?').and_then(|base| scope.get(base)) {
        *name = format!("{symbol}?");
    }
}

/// Rewrite every nominal name inside `ty` through `scope`.
pub(crate) fn rewrite_type(ty: &mut Type, scope: &FlattenStructScope) {
    match ty {
        Type::Simple(name) => rewrite_name(name, scope),
        Type::Generic { name, args } => {
            rewrite_name(name, scope);
            args.iter_mut().for_each(|arg| rewrite_type(arg, scope));
        }
        Type::Capability { inner, .. } | Type::Pointer { inner, .. } | Type::Optional(inner) => {
            rewrite_type(inner, scope)
        }
        Type::Array { element, .. } | Type::Simd { element, .. } => rewrite_type(element, scope),
        Type::Tuple(items) | Type::Union(items) => items.iter_mut().for_each(|item| rewrite_type(item, scope)),
        Type::LabeledTuple(fields) => fields.iter_mut().for_each(|field| rewrite_type(&mut field.ty, scope)),
        Type::Function { params, ret } => {
            params.iter_mut().for_each(|param| rewrite_type(param, scope));
            if let Some(ret) = ret {
                rewrite_type(ret, scope);
            }
        }
        Type::Constructor { target, args } => {
            rewrite_type(target, scope);
            if let Some(args) = args {
                args.iter_mut().for_each(|arg| rewrite_type(arg, scope));
            }
        }
        Type::TypeBinding { value, .. } => rewrite_type(value, scope),
        Type::DynTrait(_)
        | Type::UnitWithRepr { .. }
        | Type::SelfType
        | Type::ConstKeySet { .. }
        | Type::DependentKeys { .. } => {}
    }
}

fn rewrite_signature(function: &mut simple_parser::ast::FunctionDef, scope: &FlattenStructScope) {
    if scope.is_empty() {
        return;
    }
    for param in &mut function.params {
        if let Some(ty) = &mut param.ty {
            rewrite_type(ty, scope);
        }
    }
    if let Some(ty) = &mut function.return_type {
        rewrite_type(ty, scope);
    }
}

/// Rename colliding struct/class declarations to owner-exact symbols and
/// rewrite declaration signatures through each declaring owner's scope.
///
/// Returns `None` when no struct/class name collides.
///
/// `Err(alias)` when a type alias names a colliding struct (no owner to
/// resolve it through).
pub(crate) fn module_with_owner_qualified_structs(
    ast_module: &Module,
    bindings: &FlattenImportBindings,
    globs: &FlattenGlobSources,
) -> Result<Option<(Module, FlattenStructOwners)>, String> {
    let owners = census(&ast_module.items);
    if owners.is_empty() {
        return Ok(None);
    }
    let mut scopes: HashMap<Option<String>, FlattenStructScope> = HashMap::new();
    let mut scope_of = |owner: &Option<String>| -> FlattenStructScope {
        scopes
            .entry(owner.clone())
            .or_insert_with(|| struct_scope_for(&owners, bindings, globs, owner.as_deref()))
            .clone()
    };

    let mut module = ast_module.clone();
    let mut pending_global_owner: Option<String> = None;
    for item in &mut module.items {
        let global_owner = pending_global_owner.take();
        match item {
            Node::Const(c) if c.name.starts_with(FLATTEN_GLOBAL_OWNER_MARKER_PREFIX) => {
                pending_global_owner = c
                    .name
                    .strip_prefix(FLATTEN_GLOBAL_OWNER_MARKER_PREFIX)
                    .map(str::to_string);
            }
            Node::Struct(s) => {
                let owner = declaration_owner(&s.attributes, &s.methods);
                if let Some(list) = owners.get(&s.name) {
                    s.name = flattened_global_symbol(list, owner.as_deref(), &s.name);
                }
                let scope = scope_of(&owner);
                s.fields
                    .iter_mut()
                    .for_each(|field| rewrite_type(&mut field.ty, &scope));
                s.methods
                    .iter_mut()
                    .for_each(|method| rewrite_signature(method, &scope));
            }
            Node::Class(c) => {
                let owner = declaration_owner(&c.attributes, &c.methods);
                if let Some(list) = owners.get(&c.name) {
                    c.name = flattened_global_symbol(list, owner.as_deref(), &c.name);
                }
                let scope = scope_of(&owner);
                c.fields
                    .iter_mut()
                    .for_each(|field| rewrite_type(&mut field.ty, &scope));
                c.methods
                    .iter_mut()
                    .for_each(|method| rewrite_signature(method, &scope));
            }
            Node::Impl(i) => {
                let scope = scope_of(&declaration_owner(&i.attributes, &i.methods));
                rewrite_type(&mut i.target_type, &scope);
                i.methods
                    .iter_mut()
                    .for_each(|method| rewrite_signature(method, &scope));
            }
            Node::Function(f) => {
                let scope = scope_of(&Lowerer::flatten_owner_of(f.attributes.iter().map(|a| a.name.as_str())));
                rewrite_signature(f, &scope);
            }
            Node::Let(l) => {
                if let Some(ty) = &mut l.ty {
                    rewrite_type(ty, &scope_of(&global_owner));
                }
            }
            Node::Enum(e) => {
                let owner = declaration_owner(&e.attributes, &e.methods);
                if let Some(list) = owners.get(&e.name) {
                    e.name = flattened_global_symbol(list, owner.as_deref(), &e.name);
                }
                let scope = scope_of(&owner);
                for variant in &mut e.variants {
                    if let Some(fields) = &mut variant.fields {
                        fields.iter_mut().for_each(|field| rewrite_type(&mut field.ty, &scope));
                    }
                }
                e.methods.iter_mut().for_each(|method| rewrite_signature(method, &scope));
            }
            Node::Trait(t) => {
                let owner = Lowerer::flatten_owner_of(
                    t.methods.iter().flat_map(|m| m.attributes.iter().map(|a| a.name.as_str())),
                );
                let scope = scope_of(&owner);
                t.methods.iter_mut().for_each(|method| rewrite_signature(method, &scope));
            }
            // A type alias carries no owner, so a target naming a colliding
            // struct cannot be attributed. Refuse it (the caller fails the
            // lowering, i.e. the old fail-closed de-JIT) rather than bind
            // the default owner's layout silently.
            Node::TypeAlias(alias) if type_names_any(&alias.ty, &owners) => {
                return Err(alias.name.clone());
            }
            _ => {}
        }
    }
    Ok(Some((module, owners)))
}

/// Whether `ty` names any colliding struct/class (directly or nested).
fn type_names_any(ty: &Type, owners: &FlattenStructOwners) -> bool {
    let mut probe = ty.clone();
    let marker: FlattenStructScope = owners.keys().map(|name| (name.clone(), String::new())).collect();
    rewrite_type(&mut probe, &marker);
    probe != *ty
}
