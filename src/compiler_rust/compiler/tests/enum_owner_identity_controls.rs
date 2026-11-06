use simple_compiler::{hir, interpreter, mir};
use simple_compiler::codegen::JitCompiler;
use simple_parser::{ast::{Attribute, Node}, Module, Parser};

fn owned(source: &str, owner: &str) -> Vec<Node> {
    let mut module = Parser::new(source).parse().expect("owner fixture grammar");
    for node in &mut module.items {
        let (attributes, span) = match node {
            Node::Enum(def) => (&mut def.attributes, def.span),
            Node::Function(def) => (&mut def.attributes, def.span),
            Node::Impl(def) => (&mut def.attributes, def.span),
            _ => continue,
        };
        attributes.push(Attribute {
            span, name: format!("__simple_flatten_module_owner__={owner}"),
            value: None, args: None, named_args: None,
        });
    }
    module.items
}

fn module(a: &str, b: &str, body: &str) -> Module {
    let root = tempfile::tempdir().expect("owner fixture paths");
    let a_path = root.path().join("a.spl").to_string_lossy().into_owned();
    let b_path = root.path().join("b.spl").to_string_lossy().into_owned();
    let mut items = owned(a, &a_path);
    items.extend(owned(b, &b_path));
    let tail = format!("fn main() -> i64:\n{body}\n");
    items.extend(Parser::new(&tail).parse().expect("consumer grammar").items);
    Module { name: None, items }
}

fn interpreted(module: &Module) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let mut items = module.items.clone();
    items.extend(Parser::new("main = main()\n").parse().unwrap().items);
    interpreter::evaluate_module(&items).expect("interpreter control executes")
}

const A: &str = "enum Mode:\n    Alpha\n    Shared\n    Payload(value: i64)\n    fn label(self) -> text:\n        \"a\"\n\nfn a_shared() -> Mode:\n    Mode.Shared\n\nfn a_payload() -> Mode:\n    Mode.Payload(7)\n\nfn a_accept(value) -> i64:\n    match value:\n        case Mode.Shared: 11\n        case _: 12\n\nfn a_ctor():\n    Mode.Payload\n\nfn a_type():\n    Mode\n\nfn choose(value: Mode) -> i64:\n    31\n";
const B: &str = "enum Mode:\n    Beta\n    Shared\n    Payload(value: i64)\n    fn label(self) -> text:\n        \"b\"\n\nfn b_shared() -> Mode:\n    Mode.Shared\n\nfn b_payload() -> Mode:\n    Mode.Payload(7)\n\nfn choose(value: Mode) -> i64:\n    32\n";

#[test]
fn pattern_methods_and_display_follow_the_value_declaration() {
    assert_eq!(interpreted(&module(A, B,
        "    if a_accept(a_shared()) != 11: return 1\n    if a_accept(b_shared()) != 12: return 2\n    if a_shared().label() != \"a\": return 3\n    if b_shared().label() != \"b\": return 4\n    if \"{a_shared()}\" != \"Mode::Shared\": return 5\n    if \"{a_payload()}\" != \"Mode::Payload(7)\": return 6\n    return 0")), 0);
}

#[test]
fn captured_types_and_constructors_do_not_rebind_in_the_consumer() {
    assert_eq!(interpreted(&module(A, B,
        "    val constructor = a_ctor()\n    val value = constructor(7)\n    if value != a_payload(): return 1\n    if value == b_payload(): return 2\n    val type_value = a_type()\n    if type_value.Shared != a_shared(): return 3\n    if type_value.Shared == b_shared(): return 4\n    return 0")), 0);
}

#[test]
fn owner_qualified_annotations_select_the_matching_overload() {
    assert_eq!(interpreted(&module(A, B,
        "    if choose(a_shared()) != 31: return 1\n    if choose(b_shared()) != 32: return 2\n    return 0")), 0);
}

#[test]
fn custom_result_declaration_does_not_take_the_builtin_reserved_family() {
    let a = "enum Result:\n    Custom\n\nfn custom_result() -> Result:\n    Result.Custom\n\nenum Option:\n    Custom\n\nfn custom_option() -> Option:\n    Option.Custom\n";
    let b = "extern fn rt_enum_id<T>(value: T) -> i64\n";
    assert_eq!(interpreted(&module(a, b,
        "    if rt_enum_id(custom_result()) <= 1: return 1\n    if rt_enum_id(Ok(7)) != 0: return 2\n    if rt_enum_id(Some(7)) != 1: return 3\n    if rt_enum_id(custom_option()) <= 1: return 4\n    return 0")), 0);
}

#[test]
fn native_and_interpreted_construction_use_identical_owner_family_ids() {
    let a = "enum Mode:\n    Alpha\n    Shared\n\nfn a_shared() -> Mode:\n    Mode.Shared\n";
    let b = "enum Mode:\n    Beta\n    Shared\n\nextern fn rt_enum_id<T>(value: T) -> i64\n";
    let ast = module(a, b, "    rt_enum_id(a_shared())");
    let expected = interpreted(&ast);
    assert!(expected > 1, "user enum must not use a reserved builtin family ID");
    let hir = hir::lower(&ast).expect("owner identity HIR");
    let mir = mir::lower_to_mir(&hir).expect("owner identity MIR");
    let mut jit = JitCompiler::new_static().expect("static native JIT");
    jit.compile_module(&mir).expect("owner identity native compilation");
    let actual = unsafe { jit.call_i64_void("main").expect("owner identity native execution") };
    assert_eq!(actual, i64::from(expected), "family identity changed between interpreter and native construction");
}

#[test]
fn native_construction_preserves_builtins_beside_custom_same_named_enums() {
    let a = "enum Result:\n    Custom\n\nfn custom_result() -> Result:\n    Result.Custom\n\nenum Option:\n    Custom\n\nfn custom_option() -> Option:\n    Option.Custom\n";
    let b = "extern fn rt_enum_id<T>(value: T) -> i64\n";
    let ast = module(a, b, "    if rt_enum_id(custom_result()) <= 1: return 1\n    if rt_enum_id(custom_option()) <= 1: return 2\n    if rt_enum_id(Ok(7)) != 0: return 3\n    if rt_enum_id(Some(7)) != 1: return 4\n    return 0");
    assert_eq!(interpreted(&ast), 0);
    let hir = hir::lower(&ast).expect("builtin/custom family HIR");
    let mir = mir::lower_to_mir(&hir).expect("builtin/custom family MIR");
    let mut jit = JitCompiler::new_static().expect("static native JIT");
    jit.compile_module(&mir).expect("builtin/custom family native compilation");
    let result = unsafe { jit.call_i64_void("main").expect("builtin/custom family native execution") };
    assert_eq!(result, 0);
}

fn bind(mut module: Module, local: &str, source_name: &str, second: bool) -> Module {
    let owner = module.items.iter().filter_map(|node| match node {
        Node::Enum(def) => def.attributes.iter().find_map(|a|
            a.name.strip_prefix("__simple_flatten_module_owner__=").map(str::to_owned)),
        _ => None,
    }).nth(usize::from(second)).expect("fixture declaring owner");
    let mut marker = Parser::new("const marker = 0\n").parse().unwrap().items.remove(0);
    let Node::Const(ref mut declaration) = marker else { panic!("marker declaration"); };
    let importer = "<entry>";
    declaration.name = format!("__simple_flatten_import_binding__={}:{}{}:{}{}:{}{}:{}",
        importer.len(), importer, local.len(), local, owner.len(), owner, source_name.len(), source_name);
    module.items.push(marker);
    module
}

#[test]
fn selective_alias_retains_the_original_enum_identity() {
    let ast = bind(module(A, B,
        "    if AMode.Shared != a_shared(): return 1\n    if AMode.Shared == b_shared(): return 2\n    return 0"), "AMode", "Mode", false);
    assert_eq!(interpreted(&ast), 0);
}

#[test]
fn a_glob_with_one_declaring_owner_keeps_exact_identity() {
    let ast = bind(module(A, B,
        "    if Mode.Shared != a_shared(): return 1\n    if Mode.Shared == b_shared(): return 2\n    return 0"), "*", "*", false);
    assert_eq!(interpreted(&ast), 0);
}

#[test]
fn ambiguous_globs_do_not_choose_the_last_enum() {
    let ast = bind(bind(module(A, B, "    Mode.Shared\n    return 0"), "*", "*", false), "*", "*", true);
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let mut items = ast.items.clone();
    items.extend(Parser::new("main = main()\n").parse().unwrap().items);
    let failure = interpreter::evaluate_module(&items).expect_err("ambiguous enum must fail closed");
    assert!(failure.to_string().contains("Mode"));
}

#[test]
fn true_type_alias_uses_the_explicit_import_owner_before_ambiguity_check() {
    let mut ast = bind(module(A, B, "    if accept_alias(a_shared()) != 41: return 1\n    return 0"), "Mode", "Mode", false);
    ast.items.extend(Parser::new("type Selected = Mode\nfn accept_alias(value: Selected) -> i64:\n    41\n").parse().expect("true type alias grammar").items);
    assert_eq!(interpreted(&ast), 0);
}

const CARRIED_BUILTIN_CONSUMER: &str = "enum Option:\n    Custom\nenum Result:\n    Custom\nfn apply_type(type_value):\n    type_value.Some(7)\nfn apply_ok(type_value):\n    type_value.Ok(7)\nfn apply_err(type_value):\n    type_value.Err(7)\nfn custom_option_type():\n    Option\nfn custom_result_type():\n    Result\nfn apply_custom(type_value):\n    type_value.Custom\n";
const CARRIED_BUILTIN_PROVIDER: &str = "extern fn rt_enum_id<T>(value: T) -> i64\nfn builtin_type():\n    Option\nfn builtin_result_type():\n    Result\n";
const CARRIED_BUILTIN_CHECKS: &str = "    if rt_enum_id(apply_type(builtin_type())) != 1: return 1\n    if rt_enum_id(apply_ok(builtin_result_type())) != 0: return 2\n    if rt_enum_id(apply_err(builtin_result_type())) != 0: return 3\n    if rt_enum_id(apply_custom(custom_option_type())) <= 1: return 4\n    if rt_enum_id(apply_custom(custom_result_type())) <= 1: return 5\n    return 0";

#[test]
fn captured_builtin_type_does_not_rebind_to_a_custom_same_named_enum() {
    let ast = module(CARRIED_BUILTIN_CONSUMER, CARRIED_BUILTIN_PROVIDER, CARRIED_BUILTIN_CHECKS);
    assert_eq!(interpreted(&ast), 0);
}

#[test]
fn captured_actual_provider_types_preserve_reserved_ids_beside_custom_same_names() {
    let mut ast = actual_stdlib_families(CARRIED_BUILTIN_CHECKS);
    let carrier_modules = module(CARRIED_BUILTIN_CONSUMER, CARRIED_BUILTIN_PROVIDER, "    return 0");
    ast.items.extend(carrier_modules.items.into_iter().filter(|node| match node {
        Node::Function(def) => def.name != "main" && def.name != "rt_enum_id",
        _ => true,
    }));
    assert_eq!(interpreted(&ast), 0);
}

fn actual_stdlib_families(body: &str) -> Module {
    let core = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lib/std/src/core");
    let mut items = Vec::new();
    for filename in ["option.spl", "result.spl"] {
        let path = core.join(filename).canonicalize().expect("actual stdlib provider path");
        let source = std::fs::read_to_string(&path).expect("actual stdlib declaration source");
        let mut nodes = owned(&source, &path.to_string_lossy());
        for node in &mut nodes {
            if let Node::Enum(def) = node {
                def.attributes.push(Attribute { span: def.span,
                    name: format!("\0simple_selected_builtin_enum_origin={}", path.to_string_lossy()),
                    value: None, args: None, named_args: None });
            }
        }
        items.extend(nodes.into_iter().filter(|node| matches!(node, Node::Enum(_))));
    }
    let tail = format!(r#"
extern fn rt_enum_id<T>(value: T) -> i64
fn failed() -> Result<i64, text>:
    Err("sentinel")
fn propagate() -> Result<i64, text>:
    Ok(failed()?)
fn absent() -> Option<i64>:
    None
fn propagate_absent() -> Option<i64>:
    Some(absent()?)
fn main() -> i64:
{body}
"#);
    items.extend(Parser::new(&tail).parse().expect("actual stdlib control grammar").items);
    Module { name: None, items }
}

const REAL_STDLIB_CHECKS: &str = "    if rt_enum_id(Option.Some(7)) != 1: return 1\n    if rt_enum_id(Result.Ok(7)) != 0: return 2\n    match propagate():\n        case Err(error):\n            if error != \"sentinel\": return 3\n        case _: return 4\n    match propagate_absent():\n        case None: pass\n        case _: return 5\n    return 0";

#[test]
fn tagged_actual_stdlib_declarations_keep_reserved_ids_and_try_pattern_behavior() {
    assert_eq!(interpreted(&actual_stdlib_families(REAL_STDLIB_CHECKS)), 0);
}

#[test]
fn tagged_actual_stdlib_declarations_keep_native_reserved_ids() {
    let ast = actual_stdlib_families("    if rt_enum_id(Option.Some(7)) != 1: return 1\n    if rt_enum_id(Result.Ok(7)) != 0: return 2\n    return 0");
    let hir = hir::lower(&ast).expect("actual stdlib family HIR");
    let mir = mir::lower_to_mir(&hir).expect("actual stdlib family MIR");
    let mut jit = JitCompiler::new_static().expect("static native JIT");
    jit.compile_module(&mir).expect("actual stdlib native compilation");
    let result = unsafe { jit.call_i64_void("main").expect("actual stdlib native execution") };
    assert_eq!(result, 0);
}
