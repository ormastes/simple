//! Function-level reachability for the seed JIT.
//!
//! `run_file_jit` lowers the whole flattened import closure: every imported
//! `src/lib` function body becomes a MIR function whether or not anything can
//! call it (caret `--help`: 9,639 functions). Each unreachable body still costs
//! codegen time and, worse, any extern it calls counts toward the hybrid
//! interpreter splice. [`retain_reachable_functions`] drops the bodies no root
//! can reach.
//!
//! # Soundness rule
//!
//! Codegen binds a callee name to a function through several spellings: the
//! exact name, `.` -> `_dot_` sanitising, `Type__method` / module-prefix
//! mangling, `strip_call_module_prefix`, SFFI aliases, and
//! `FuncIdTable::resolve_unique_module_qualified`, which binds a probe to the
//! UNIQUE function sharing its tail. Removing a function could therefore turn
//! an ambiguous tail into a unique one and silently rebind a call. To rule
//! that out, names are matched by KEY rather than exactly: a name's keys are
//! the name itself, its separator-normalised form, and every suffix that
//! follows a separator (`::`, `.`, `_dot_`, `__`, at every position). A
//! function is kept when any of its keys equals a key of any name a reachable
//! function mentions. In particular every function that shares a probed tail
//! stays, so tail resolution sees exactly the candidates it saw before.
//!
//! Names are collected from every string an instruction carries: the
//! name-bearing variants explicitly, a list of hot variants that carry no
//! string skipped, and every other variant through its `Debug` text (each
//! quoted string). A new instruction kind is therefore covered by default.
//! A method name alone (`BuiltinMethod`, `MethodCallStatic`, vtable type
//! switches) keeps every `T.method` / `T__method`, so by-name dispatch over
//! receiver types is preserved.
//!
//! Roots: `main`, every `__module_init*` function (static/global
//! initialisers, run before `main`), function-valued global initialisers,
//! every vtable slot (vtables are emitted for every impl, so trait dispatch
//! can reach any slot), functions carrying one of [`ROOT_ATTRIBUTES`],
//! every local body named like a `RUNTIME_FUNCS` entry (codegen-emitted runtime calls bind to it by
//! name), and the strings carried by struct-valued global initialisers.
//!
//! A missed direct-`Call` edge fails closed (undefined import -> the JIT
//! refuses the module). A missed `ClosureCreate`/`GlobalLoad`/method edge
//! would not, which is why those names are collected explicitly.

use std::collections::{HashMap, HashSet};

use super::{MirFunction, MirInst, MirModule};

/// Matching keys of a name: the name, its normalised form (`::`, `.`,
/// `_dot_` -> `__`), and every suffix after a `__` in the normalised form.
fn name_keys(name: &str, out: &mut Vec<String>) {
    out.push(name.to_string());
    let normalized = name.replace("::", "__").replace("_dot_", "__").replace('.', "__");
    let bytes = normalized.as_bytes();
    for i in 0..bytes.len().saturating_sub(1) {
        if bytes[i] == b'_' && bytes[i + 1] == b'_' && i + 2 < bytes.len() {
            out.push(normalized[i + 2..].to_string());
        }
    }
    out.push(normalized);
}

/// Every quoted string in a `Debug` rendering (escapes kept verbatim; a name
/// never contains a quote or backslash, so this is exact for names).
fn debug_strings(text: &str, out: &mut Vec<String>) {
    let mut chars = text.char_indices();
    while let Some((start, c)) = chars.next() {
        if c != '"' {
            continue;
        }
        let mut escaped = false;
        let mut end = None;
        for (i, c) in chars.by_ref() {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                end = Some(i);
                break;
            }
        }
        match end {
            Some(end) => out.push(text[start + 1..end].to_string()),
            None => return,
        }
    }
}

/// Names an instruction mentions. Conservative: unknown variants go through
/// their `Debug` text.
fn instruction_names(inst: &MirInst, out: &mut Vec<String>) {
    use crate::codegen::instr::calls::{sffi_alias_target, strip_call_module_prefix};
    match inst {
        MirInst::Call { target, .. } => {
            let raw = target.name();
            out.push(raw.to_string());
            let base = strip_call_module_prefix(raw);
            out.push(base.to_string());
            if let Some(alias) = sffi_alias_target(base) {
                out.push(alias.to_string());
            }
        }
        MirInst::InterpCall { func_name, .. }
        | MirInst::ClosureCreate { func_name, .. }
        | MirInst::MethodCallStatic { func_name, .. } => out.push(func_name.clone()),
        MirInst::GlobalLoad { global_name, .. } | MirInst::GlobalStore { global_name, .. } => {
            out.push(global_name.clone())
        }
        MirInst::BuiltinMethod {
            receiver_type, method, ..
        } => {
            out.push(receiver_type.clone());
            out.push(method.clone());
        }
        MirInst::ExternMethodCall {
            class_name,
            method_name,
            ..
        } => {
            out.push(class_name.clone());
            out.push(method_name.clone());
        }
        // Hot variants that carry no string (no name can hide in them).
        MirInst::ConstInt { .. }
        | MirInst::ConstFloat { .. }
        | MirInst::ConstBool { .. }
        | MirInst::Copy { .. }
        | MirInst::BinOp { .. }
        | MirInst::UnaryOp { .. }
        | MirInst::Cast { .. }
        | MirInst::Load { .. }
        | MirInst::Store { .. }
        | MirInst::LocalAddr { .. }
        | MirInst::GetElementPtr { .. }
        | MirInst::BoxInt { .. }
        | MirInst::BoxFloat { .. }
        | MirInst::UnboxInt { .. }
        | MirInst::UnboxFloat { .. }
        | MirInst::IndexGet { .. }
        | MirInst::IndexSet { .. }
        | MirInst::Drop { .. }
        | MirInst::EndScope { .. } => {}
        other => debug_strings(&format!("{other:?}"), out),
    }
}

fn function_names(func: &MirFunction, out: &mut Vec<String>) {
    for block in &func.blocks {
        for inst in &block.instructions {
            instruction_names(inst, out);
        }
    }
    for body in func.outlined_bodies.values() {
        out.push(body.name.clone());
    }
}

/// Attributes that publish a function under its own name to something other
/// than MIR calls. (Every flattened function carries the bookkeeping
/// attributes `actor` and `__simple_flatten_module_owner__=...`, so "has any
/// attribute" would root the whole module.)
const ROOT_ATTRIBUTES: &[&str] = &["export", "no_mangle", "entry", "init", "constructor", "used"];

fn is_root(func: &MirFunction) -> bool {
    func.name == "main"
        || func.name.starts_with("__module_init")
        // Codegen emits runtime calls of its own (`rt_native_eq` for `BinOp`,
        // `rt_index_get`, ...) and `resolve_runtime_func` prefers a same-named
        // MIR body; no instruction names them, so keep every local body that
        // shadows a codegen runtime function (`call_runtime_*` only emits
        // names from `RUNTIME_FUNCS`).
        || crate::codegen::runtime_sffi::spec_for(&func.name).is_some()
        || func.attributes.iter().any(|a| ROOT_ATTRIBUTES.contains(&a.as_str()))
}

/// Names of the functions reachable from the module's roots (see the module
/// docs for the roots and the matching rule).
pub fn reachable_function_names(module: &MirModule) -> HashSet<String> {
    // key -> indices of the functions carrying that key.
    let mut by_key: HashMap<String, Vec<usize>> = HashMap::new();
    let mut keys = Vec::new();
    for (index, func) in module.functions.iter().enumerate() {
        keys.clear();
        name_keys(&func.name, &mut keys);
        for key in keys.drain(..) {
            let bucket = by_key.entry(key).or_default();
            if bucket.last() != Some(&index) {
                bucket.push(index);
            }
        }
    }

    let mut reached = vec![false; module.functions.len()];
    let mut worklist: Vec<usize> = Vec::new();
    let mut seen_keys: HashSet<String> = HashSet::new();
    let mut names: Vec<String> = Vec::new();

    // Roots by name.
    names.extend(module.global_init_functions.values().cloned());
    for (_, _, _, slots, _) in &module.vtable_impls {
        names.extend(slots.iter().flatten().cloned());
    }
    for init in module.global_init_structs.values() {
        debug_strings(&format!("{init:?}"), &mut names);
    }
    for (index, func) in module.functions.iter().enumerate() {
        if is_root(func) {
            reached[index] = true;
            worklist.push(index);
        }
    }

    loop {
        for name in names.drain(..) {
            keys.clear();
            name_keys(&name, &mut keys);
            for key in keys.drain(..) {
                if !seen_keys.insert(key.clone()) {
                    continue;
                }
                if let Some(bucket) = by_key.get(&key) {
                    for &index in bucket {
                        if !reached[index] {
                            reached[index] = true;
                            worklist.push(index);
                        }
                    }
                }
            }
        }
        let Some(index) = worklist.pop() else { break };
        function_names(&module.functions[index], &mut names);
    }

    module
        .functions
        .iter()
        .zip(reached)
        .filter(|(_, r)| *r)
        .map(|(f, _)| f.name.clone())
        .collect()
}

/// Drop every function no root can reach. Returns `(before, after)` counts.
/// Duplicate-named functions (a declaration and a body) are kept or dropped
/// together.
pub fn retain_reachable_functions(module: &mut MirModule) -> (usize, usize) {
    let before = module.functions.len();
    let keep = reachable_function_names(module);
    module.functions.retain(|f| keep.contains(&f.name));
    (before, module.functions.len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::TypeId;
    use crate::mir::{CallTarget, VReg};

    fn func(name: &str, instructions: Vec<MirInst>) -> MirFunction {
        let mut f = MirFunction::new(name.to_string(), TypeId::I64, simple_parser::Visibility::Private);
        let entry = f.entry_block;
        let block = f.block_mut(entry).unwrap();
        block.instructions = instructions;
        block.terminator = crate::mir::Terminator::Return(Some(VReg(0)));
        f
    }

    fn call(name: &str) -> MirInst {
        MirInst::Call {
            dest: Some(VReg(0)),
            target: CallTarget::Pure(name.to_string()),
            args: vec![],
        }
    }

    fn module(funcs: Vec<MirFunction>) -> MirModule {
        let mut m = MirModule::new();
        m.functions = funcs;
        m
    }

    #[test]
    fn unreachable_function_is_dropped_and_callees_kept() {
        let mut m = module(vec![
            func("main", vec![call("helper")]),
            func("helper", vec![call("leaf")]),
            func("leaf", vec![]),
            func("dead", vec![call("rt_dead_extern")]),
        ]);
        assert_eq!(retain_reachable_functions(&mut m), (4, 3));
        let names: Vec<_> = m.functions.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(names, ["main", "helper", "leaf"]);
    }

    #[test]
    fn every_function_sharing_a_probed_tail_is_kept() {
        // A probe `foo` may bind to the unique `<prefix>__foo`; both must
        // stay, or removing one would make the other unique.
        let mut m = module(vec![
            func("main", vec![call("foo")]),
            func("a__foo", vec![]),
            func("b__foo", vec![]),
            func("Type.foo", vec![]),
            func("unrelated", vec![]),
        ]);
        let keep = reachable_function_names(&m);
        for name in ["main", "a__foo", "b__foo", "Type.foo"] {
            assert!(keep.contains(name), "{name} dropped: {keep:?}");
        }
        assert!(!keep.contains("unrelated"));
        retain_reachable_functions(&mut m);
        assert_eq!(m.functions.len(), 4);
    }

    #[test]
    fn mangled_call_reaches_bare_function_and_private_helper() {
        let m = module(vec![
            func("main", vec![call("mod__bar"), call("_index_of")]),
            func("bar", vec![]),
            func("m___index_of", vec![]),
        ]);
        let keep = reachable_function_names(&m);
        assert!(keep.contains("bar") && keep.contains("m___index_of"), "{keep:?}");
    }

    #[test]
    fn function_values_closures_static_methods_and_builtin_methods_are_edges() {
        let m = module(vec![
            func(
                "main",
                vec![
                    MirInst::GlobalLoad {
                        dest: VReg(1),
                        global_name: "fn_value".to_string(),
                        ty: TypeId::I64,
                    },
                    MirInst::ClosureCreate {
                        dest: VReg(2),
                        func_name: "lambda_body".to_string(),
                        closure_size: 8,
                        capture_offsets: vec![],
                        capture_types: vec![],
                        captures: vec![],
                        lambda_params: vec![],
                        body_block: None,
                        return_type: TypeId::I64,
                    },
                    MirInst::MethodCallStatic {
                        dest: None,
                        receiver: VReg(0),
                        func_name: "Shape.area".to_string(),
                        args: vec![],
                    },
                ],
            ),
            func("fn_value", vec![]),
            func("lambda_body", vec![]),
            func("Circle.area", vec![]),
            func("Square__area", vec![]),
            func("dead", vec![]),
        ]);
        let keep = reachable_function_names(&m);
        for name in ["fn_value", "lambda_body", "Circle.area", "Square__area"] {
            assert!(keep.contains(name), "{name} dropped: {keep:?}");
        }
        assert!(!keep.contains("dead"));
    }

    #[test]
    fn roots_cover_init_vtables_global_fn_values_and_attributes() {
        let mut exported = func("exported_cb", vec![]);
        exported.attributes.push("export".to_string());
        let mut bookkeeping = func("dead_with_bookkeeping_attrs", vec![]);
        bookkeeping.attributes.push("actor".to_string());
        bookkeeping
            .attributes
            .push("__simple_flatten_module_owner__=/x.spl".to_string());
        let mut m = module(vec![
            func("main", vec![]),
            func("__module_init_app_dynamic", vec![call("init_helper")]),
            func("init_helper", vec![]),
            func("Circle.draw", vec![call("draw_helper")]),
            func("draw_helper", vec![]),
            func("global_fn", vec![]),
            exported,
            func("rt_native_eq", vec![]),
            bookkeeping,
            func("dead", vec![]),
        ]);
        m.vtable_impls.push((
            TypeId::I64,
            "Circle".to_string(),
            "__vtable__Circle__for__Drawable".to_string(),
            vec![None, Some("Circle.draw".to_string())],
            false,
        ));
        m.global_init_functions.insert("g".to_string(), "global_fn".to_string());
        let keep = reachable_function_names(&m);
        for name in [
            "main",
            "__module_init_app_dynamic",
            "init_helper",
            "Circle.draw",
            "draw_helper",
            "global_fn",
            "exported_cb",
            "rt_native_eq",
        ] {
            assert!(keep.contains(name), "{name} dropped: {keep:?}");
        }
        assert!(!keep.contains("dead"));
        assert!(!keep.contains("dead_with_bookkeeping_attrs"));
    }

    #[test]
    fn unknown_variants_are_scanned_through_debug_text() {
        let m = module(vec![
            func(
                "main",
                vec![MirInst::ConstSymbol {
                    dest: VReg(0),
                    value: "by_name_target".to_string(),
                }],
            ),
            func("by_name_target", vec![]),
        ]);
        assert!(reachable_function_names(&m).contains("by_name_target"));
    }

    #[test]
    fn debug_strings_extracts_quoted_strings_with_escapes() {
        let mut out = Vec::new();
        debug_strings(r#"X { a: "one", b: Some("t\"wo"), c: 3 }"#, &mut out);
        assert_eq!(out, ["one", r#"t\"wo"#]);
    }
}
