//! Regression for
//! `doc/08_tracking/bug/native_codegen_trait_field_receiver_erased_ambiguous_2026_10_26.md`.
//!
//! A trait-typed FIELD receiver (`self.store.read(k)`) used to lower to a bare
//! `read` MethodCallStatic because the trait type aliases to ANY and only
//! typed LOCALS carried the declared trait owner; the native linker then saw
//! every same-named `*.read` as a candidate (AMBIGUOUS-METHOD).
use super::parse_and_lower;
use crate::mir::MirInst;

const SRC: &str = "trait Store:\n    fn read(key: i64) -> i64\n\nclass Disk:\n    var n: i64\n    fn read(key: i64) -> i64:\n        key\n\nclass Net:\n    var n: i64\n    fn read(key: i64) -> i64:\n        key + 1\n\nclass Adapter:\n    var store: Store\n    fn get(key: i64) -> i64:\n        self.store.read(key)\n";

#[test]
fn trait_typed_field_receiver_lowers_to_vtable_dispatch() {
    let module = parse_and_lower(SRC).unwrap();
    let mir = crate::mir::lower_to_mir(&module).expect("lower to mir");
    let get = mir.functions.iter().find(|f| f.name.ends_with("get")).expect("Adapter.get");
    let insts: Vec<_> = get.blocks.iter().flat_map(|b| &b.instructions).collect();
    assert!(
        insts.iter().any(|i| matches!(i, MirInst::MethodCallVirtual { vtable_slot: 0, .. })),
        "trait field receiver must dispatch through the Store vtable: {insts:?}"
    );
    assert!(
        !insts.iter().any(|i| matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name == "read")),
        "bare ambiguous `read` must not be emitted: {insts:?}"
    );
}

/// `val s = self.store` (unannotated local initialised from a trait-typed
/// field) must carry the field's trait owner, exactly like `val s: Store = ...`.
/// doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md (row 1)
const LOCAL_SRC: &str = "trait Store:\n    fn read(key: i64) -> i64\n\nclass Disk:\n    var n: i64\n    fn read(key: i64) -> i64:\n        key\n\nclass Net:\n    var n: i64\n    fn read(key: i64) -> i64:\n        key + 1\n\nclass Adapter:\n    var store: Store\n\nfn get(a: Adapter, key: i64) -> i64:\n    val s = a.store\n    s.read(key)\n";

#[test]
fn trait_typed_field_initialised_local_lowers_to_vtable_dispatch() {
    let module = parse_and_lower(LOCAL_SRC).unwrap();
    let mir = crate::mir::lower_to_mir(&module).expect("lower to mir");
    let get = mir.functions.iter().find(|f| f.name == "get").expect("get");
    let insts: Vec<_> = get.blocks.iter().flat_map(|b| &b.instructions).collect();
    assert!(
        insts.iter().any(|i| matches!(i, MirInst::MethodCallVirtual { vtable_slot: 0, .. })),
        "field-initialised trait local must dispatch through the Store vtable: {insts:?}"
    );
    assert!(
        !insts.iter().any(|i| matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name == "read")),
        "bare ambiguous `read` must not be emitted: {insts:?}"
    );
}


// No concrete implementation is present: the exact declared payload table
// must suffice to emit a virtual call instead of a bare unresolved symbol.
const OPTIONAL_FIELDS: &str = r#"
trait Reader:
    fn read() -> i64
trait Other<T>:
    fn padding() -> i64
    fn read() -> i64
class Holder:
    first: Reader?
    second: Other<i64>?
    noise: Any?
    fn from_if() -> i64:
        if val selected_first = self.first:
            return selected_first.read()
        0
    fn from_match() -> i64:
        match self.second:
            case Some(selected_second): return selected_second.read()
            case _: return 0
    fn generic_if() -> i64:
        if val selected_generic = self.second:
            return selected_generic.read()
        0
    fn carriers():
        val whole = self.second
        match self.second:
            case untouched: 0
        if val untyped = self.noise:
            0
fn generic_param(value: Other<i64>?) -> i64:
    if val selected_param = value:
        return selected_param.read()
    0
"#;

#[test]
fn optional_trait_field_payloads_keep_exact_declared_tables() {
    let module = parse_and_lower(OPTIONAL_FIELDS).expect("lower optional trait fields");
    for (function, local, owner, slot) in [
        ("from_if", "selected_first", "Reader", 0),
        ("from_match", "selected_second", "Other", 1),
        ("generic_if", "selected_generic", "Other", 1),
        ("generic_param", "selected_param", "Other", 1),
    ] {
        let function = module.functions.iter().find(|f| f.name.ends_with(function)).unwrap();
        let binding = function.locals.iter().find(|l| l.name == local).unwrap();
        let dispatch = binding.trait_dispatch_owner.as_ref().expect("payload's declared trait owner");
        assert!(dispatch.owner.ends_with(&format!("::{owner}")), "{}", dispatch.owner);
        assert_eq!(dispatch.info.get_vtable_slot("read"), Some(slot));
        assert!(binding.type_name_hint.is_none(), "dispatch must not invent capability/type-name hints");
    }
    let carriers = module.functions.iter().find(|f| f.name.ends_with("carriers")).unwrap();
    for name in ["whole", "untouched", "untyped"] {
        let local = carriers.locals.iter().find(|l| l.name == name).unwrap();
        assert!(local.trait_dispatch_owner.is_none(), "Option/Any carrier {name} acquired trait authority");
    }
    let mir = crate::mir::lower_to_mir(&module).expect("lower exact payload calls");
    for (name, slot) in [("from_if", 0), ("from_match", 1), ("generic_if", 1), ("generic_param", 1)] {
        let function = mir.functions.iter().find(|f| f.name.ends_with(name)).unwrap();
        let instructions: Vec<_> = function.blocks.iter().flat_map(|b| &b.instructions).collect();
        assert!(instructions.iter().any(|i| matches!(i, MirInst::MethodCallVirtual { vtable_slot, .. } if *vtable_slot == slot)), "{name}: {instructions:?}");
        assert!(!instructions.iter().any(|i| matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name == "read" || func_name.ends_with(".read"))), "bare/guessed owner call in {name}: {instructions:?}");
    }
}

#[test]
fn optional_field_and_generic_declaration_are_not_trait_carriers() {
    let module = parse_and_lower(OPTIONAL_FIELDS).expect("lower carrier negatives");
    let holder = module.functions.iter().find(|f| f.name.ends_with("carriers")).unwrap();
    assert!(holder.locals.iter().all(|local| local.trait_dispatch_owner.is_none()));
    // A same-named field in an unrelated owner must not inherit Holder.first.
    let source = format!("{OPTIONAL_FIELDS}\nclass Unrelated:\n    first: Any?\n    fn inspect():\n        if val unrelated = self.first:\n            0\n");
    let module = parse_and_lower(&source).expect("lower unrelated field owner");
    let inspect = module.functions.iter().find(|f| f.name.ends_with("inspect")).unwrap();
    assert!(inspect.locals.iter().all(|local| local.trait_dispatch_owner.is_none()));
}

#[test]
fn imported_optional_field_uses_provider_trait_alias_not_callers_same_name() {
    use crate::hir::Lowerer;
    use crate::module_resolver::ModuleResolver;
    use simple_parser::Parser;
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("src");
    std::fs::create_dir(&src).unwrap();
    std::fs::write(src.join("definition.spl"),
        "trait Reader<T>:\n    fn padding() -> i64\n    fn read() -> i64\n").unwrap();
    std::fs::write(src.join("provider.spl"),
        "use definition.{Reader as Selected}\nclass ImportedBox:\n    owner: Selected<i64>?\n").unwrap();
    let source = "use provider.{ImportedBox}\ntrait Selected<T>:\n    fn read() -> i64\nfn consume(box: ImportedBox) -> i64:\n    if val chosen = box.owner:\n        return chosen.read()\n    0\n";
    let path = src.join("main.spl");
    std::fs::write(&path, source).unwrap();
    let ast = Parser::new(source).parse().unwrap();
    let mut lowerer = Lowerer::with_module_resolver(ModuleResolver::new(dir.path().to_path_buf(), src.clone()), path);
    let module = lowerer.lower_module(&ast).expect("lower imported optional field");
    let function = module.functions.iter().find(|f| f.name == "consume").unwrap();
    let chosen = function.locals.iter().find(|l| l.name == "chosen").unwrap();
    let dispatch = chosen.trait_dispatch_owner.as_ref().expect("provider field authority");
    let provider = crate::interpreter::normalize_path_key(&src.join("definition.spl"));
    assert_eq!(dispatch.owner, format!("{}::Reader", provider.to_string_lossy()));
    assert_eq!(dispatch.info.get_vtable_slot("read"), Some(1));
    let mir = crate::mir::lower_to_mir(&module).unwrap();
    let function = mir.functions.iter().find(|f| f.name == "consume").unwrap();
    assert!(function.blocks.iter().flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::MethodCallVirtual {vtable_slot: 1, ..})));
}
