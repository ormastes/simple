use super::aot_compiles;
use crate::hir::{HirStmt, Lowerer};
use crate::mir::{BlockId, MirInst};

fn lower_body(source: &str) -> Vec<HirStmt> {
    let mut parser = simple_parser::Parser::new(source);
    let ast = parser.parse().expect("parse");
    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("lower");
    hir.functions.into_iter().find(|f| f.name == "main").expect("main").body
}

#[test]
fn codegen_inline_asm_single_instruction_collects_cli() {
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_cli", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["cli".to_string()],
            volatile: false,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c(dir.path())
        .expect("write asm c")
        .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(c.contains("\"cli\\n\""));
}

#[test]
fn codegen_inline_asm_multi_instruction_collects_cli_hlt() {
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_cli_hlt", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["cli".to_string(), "hlt".to_string()],
            volatile: false,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c(dir.path())
        .expect("write asm c")
        .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(c.contains("\"cli\\n\""));
    assert!(c.contains("\"hlt\\n\""));
}

#[test]
fn hir_inline_asm_volatile_flag_is_preserved() {
    let body = lower_body(
        r#"
fn main() -> i64:
    asm volatile { "sti" }
    return 0
"#,
    );
    assert!(matches!(
        &body[0],
        HirStmt::InlineAsm {
            instructions,
            volatile: true
        } if instructions == &vec!["sti".to_string()]
    ));
}

#[test]
fn hir_operand_bound_inline_asm_remains_noop() {
    let body = lower_body(
        r#"
fn main() -> i64:
    var x: u64 = 0
    asm volatile("mov {out}, 0", out(reg) x)
    return 0
"#,
    );
    assert!(!body.iter().any(|stmt| matches!(stmt, HirStmt::InlineAsm { .. })));
}
