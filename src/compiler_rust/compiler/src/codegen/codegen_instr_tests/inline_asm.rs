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
fn native_inline_asm_x86_target_uses_intel_syntax() {
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_x86_intel", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["mov ax, 0x28".to_string(), "ltr ax".to_string()],
            volatile: true,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target(
        dir.path(),
        Some(("x86_64-unknown-none", "", "")),
    )
    .expect("write asm c")
    .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(c.contains(".intel_syntax noprefix"));
    assert!(c.contains("\"mov ax, 0x28\\n\""));
    assert!(c.contains("\"ltr ax\\n\""));
    assert!(c.contains(".att_syntax prefix"));
}

#[test]
fn native_inline_asm_skips_unresolved_simple_operands() {
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_operand_skip", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["mov {out}, cr3".to_string()],
            volatile: true,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target(
        dir.path(),
        Some(("x86_64-unknown-none", "", "")),
    )
    .expect("write asm c")
    .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(!c.contains("mov {out}, cr3"));
    assert!(c.contains("skipped Simple asm with unresolved operands"));
}

#[test]
fn hir_inline_asm_volatile_flag_is_preserved() {
    let body = lower_body(
        r#"
fn main() -> i64:
    asm volatile { sti }
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
