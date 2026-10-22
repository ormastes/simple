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
//! else unchanged (bare). Glob imports carry no per-name marker and keep the
//! bare-name meaning.
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

/// `(name, owner, field layout)` of a struct/class declaration.
fn struct_declaration(node: &Node) -> Option<(&str, Option<String>, Vec<(&str, &Type)>)> {
    match node {
        Node::Struct(s) => Some((
            s.name.as_str(),
            declaration_owner(&s.attributes, &s.methods),
            s.fields.iter().map(|f| (f.name.as_str(), &f.ty)).collect(),
        )),
        Node::Class(c) => Some((
            c.name.as_str(),
            declaration_owner(&c.attributes, &c.methods),
            c.fields.iter().map(|f| (f.name.as_str(), &f.ty)).collect(),
        )),
        _ => None,
    }
}

fn census(items: &[Node]) -> FlattenStructOwners {
    let mut owners: FlattenStructOwners = HashMap::new();
    let mut layouts: HashMap<&str, Vec<Vec<(&str, &Type)>>> = HashMap::new();
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

/// Owner-exact symbol of the struct/class `name` as seen from `current`, or
/// `None` when nothing attributes it (keep the bare-name lookup).
pub(crate) fn resolve_owned_struct(
    owners: &FlattenStructOwners,
    bindings: &FlattenImportBindings,
    current: Option<&str>,
    name: &str,
) -> Option<String> {
    if let Some(list) = owners.get(name) {
        if list.iter().any(|owner| owner.as_deref() == current) {
            return Some(flattened_global_symbol(list, current, name));
        }
    }
    let mut importer = current.unwrap_or("<entry>");
    let mut local = name;
    for _ in 0..MAX_REEXPORT_HOPS {
        let (source_owner, source_name) = bindings.get(importer)?.get(local)?;
        if let Some(list) = owners.get(source_name) {
            if list.iter().any(|owner| owner.as_deref() == Some(source_owner.as_str())) {
                return Some(flattened_global_symbol(list, Some(source_owner), source_name));
            }
        }
        // Re-export facade: follow the source module's own import of the name.
        importer = source_owner;
        local = source_name;
    }
    None
}

/// Every bare (or aliased) name whose meaning from `current` differs from the
/// plain registry entry.
pub(crate) fn struct_scope_for(
    owners: &FlattenStructOwners,
    bindings: &FlattenImportBindings,
    current: Option<&str>,
) -> FlattenStructScope {
    let mut scope = FlattenStructScope::new();
    for name in owners.keys() {
        if let Some(symbol) = resolve_owned_struct(owners, bindings, current, name) {
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
            if let Some(symbol) = resolve_owned_struct(owners, bindings, current, local) {
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
) -> Result<Option<(Module, FlattenStructOwners)>, String> {
    let owners = census(&ast_module.items);
    if owners.is_empty() {
        return Ok(None);
    }
    let mut scopes: HashMap<Option<String>, FlattenStructScope> = HashMap::new();
    let mut scope_of = |owner: &Option<String>| -> FlattenStructScope {
        scopes
            .entry(owner.clone())
            .or_insert_with(|| struct_scope_for(&owners, bindings, owner.as_deref()))
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
                let scope = scope_of(&declaration_owner(&e.attributes, &e.methods));
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
