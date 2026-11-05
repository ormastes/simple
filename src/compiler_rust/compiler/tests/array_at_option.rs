use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn main() -> i64:
    val arr = [10, 20, 30]
    match arr.at(1):
        case Some(value):
            if value != 20: return 1
        case None:
            return 2
    match arr.at(99):
        case Some(value):
            return 3
        case None:
            match arr.at(-1):
                case Some(value):
                    return 4
                case None:
                    return 0
    return 5
"#;

fn run_interpreter() -> i64 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("source must run in interpreter") as i64
}

fn run_jit() -> i64 {
    let ast = Parser::new(SOURCE).parse().expect("source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn array_at_option_matches_on_interpreter_and_static_jit() {
    let interpreted = run_interpreter();
    let jit = run_jit();
    assert_eq!(interpreted, 0, "interpreter failed at row {interpreted}");
    assert_eq!(jit, 0, "static Cranelift JIT failed at row {jit}");
    assert_eq!(jit, interpreted, "static Cranelift JIT diverged from the interpreter");
}
