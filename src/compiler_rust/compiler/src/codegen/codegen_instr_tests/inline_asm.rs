use super::aot_compiles;
use crate::hir::{HirStmt, Lowerer};
use crate::mir::{BlockId, MirInst};
use std::sync::{Mutex, OnceLock};

fn inline_asm_test_lock() -> &'static Mutex<()> {
    static INLINE_ASM_TEST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    INLINE_ASM_TEST_LOCK.get_or_init(|| Mutex::new(()))
}

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
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_cli", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["cli".to_string()],
            volatile: false,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
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
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_cli_hlt", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["cli".to_string(), "hlt".to_string()],
            volatile: false,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
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
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_x86_intel", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["mov ax, 0x28".to_string(), "ltr ax".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
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
fn native_inline_asm_riscv_target_preserves_raw_instructions() {
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_riscv_raw", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["wfi".to_string(), "j .".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target(
        dir.path(),
        Some(("riscv64-unknown-elf", "-march=rv64imac", "-mabi=lp64")),
    )
    .expect("write asm c")
    .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(!c.contains(".intel_syntax noprefix"));
    assert!(c.contains("\"wfi\\n\""));
    assert!(c.contains("\"j .\\n\""));
}

#[test]
fn native_inline_asm_skips_unresolved_simple_operands() {
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_operand_skip", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["mov {out}, cr3".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
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
fn native_inline_asm_c_skips_simple_operand_directives() {
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_simple_operands", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec![
                "nop".to_string(),
                "in(reg) id".to_string(),
                "result = out (reg) result".to_string(),
                "inout(reg) value".to_string(),
                "lateout(reg) scratch".to_string(),
                "clobber(\"x0\")".to_string(),
                "clobber_abi(\"C\")".to_string(),
                "options(nostack)".to_string(),
            ],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c(dir.path())
        .expect("write asm c")
        .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(c.contains("\"nop\\n\""));
    assert!(!c.contains("in(reg) id"));
    assert!(!c.contains("out (reg) result"));
    assert!(!c.contains("clobber_abi"));

    let object = crate::pipeline::native_project::inline_asm_emit::compile_inline_asm_c(dir.path(), None)
        .expect("compile asm c")
        .expect("valid asm object");
    assert!(object.exists());
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
            volatile: true,
            ..
        } if instructions == &vec!["sti".to_string()]
    ));
}

#[test]
fn hir_operand_bound_inline_asm_lowers_with_operands() {
    // Until 2026-08-28 an operand-bound block was silently DROPPED (this test
    // pinned that as "remains_noop"). It now lowers with its operands.
    let body = lower_body(
        r#"
fn main() -> i64:
    var x: u64 = 0
    asm volatile("mov {out}, 0", out(reg) x)
    return 0
"#,
    );
    assert!(body.iter().any(|stmt| matches!(
        stmt,
        HirStmt::InlineAsm { operands, .. } if operands.len() == 1
    )));
}

/// Reproduce for
/// `doc/08_tracking/bug/rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md`
/// defect 1. The inline-asm registry is process-global, so entry-closure
/// discovery leaves x86 blocks in it even for a riscv64 build. RED before the
/// fix: `block_matches_target` had only an x86 arm, so `in eax, dx`,
/// `mov cr3, pd`, `out dx, eax` and `invlpg [addr]` were emitted into the
/// riscv64 translation unit and the riscv64 assembler rejected all four
/// ("unrecognized instruction mnemonic, did you mean: li?/mv?/not?",
/// "unknown operand") — 8 of that gate's 18 errors.
#[test]
fn native_inline_asm_riscv_target_rejects_x86_blocks() {
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_x86_in_riscv_tu", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["in eax, dx".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["mov cr3, pd".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["out dx, eax".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["invlpg [addr]".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        // A genuinely riscv block must survive the same filter, so the test
        // cannot pass by emitting nothing at all.
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["csrr t0, mhartid".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target(
        dir.path(),
        Some(("riscv64-unknown-elf", "-march=rv64imac", "-mabi=lp64")),
    )
    .expect("write asm c")
    .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    for x86 in ["in eax, dx", "mov cr3, pd", "out dx, eax", "invlpg [addr]"] {
        assert!(!c.contains(x86), "x86 asm leaked into the riscv64 TU: {x86}");
    }
    assert!(
        c.contains("\"csrr t0, mhartid\\n\""),
        "the riscv block must still be emitted, otherwise this test is vacuous"
    );
}

/// The reverse arm must keep working: a riscv block stays out of an x86 TU,
/// and an x86 block stays in it.
#[test]
fn native_inline_asm_x86_target_still_rejects_riscv_blocks() {
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_riscv_in_x86_tu", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["csrw mtvec, t0".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec!["cli".to_string(), "hlt".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
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
    assert!(!c.contains("csrw mtvec, t0"), "riscv asm leaked into the x86_64 TU");
    assert!(c.contains("\"hlt\\n\""), "the x86 block must still be emitted");
}

/// Defect 2, end to end through the emitter: a block-form operand placeholder
/// now reaches the C sidecar with its braces intact, so the existing
/// `has_unresolved_simple_operand` guard turns it into a skip comment instead
/// of handing `csrr 0, mcause` to the riscv64 assembler.
#[test]
fn native_inline_asm_riscv_skips_block_form_operand_placeholders() {
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    assert!(aot_compiles("inline_asm_riscv_operand_skip", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InlineAsm {
            instructions: vec![
                "csrr {0}, mcause".to_string(),
                "csrc mip, {msie}".to_string(),
                "wfi".to_string(),
            ],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));

    let dir = tempfile::tempdir().expect("tempdir");
    let c_path = crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target(
        dir.path(),
        Some(("riscv64-unknown-elf", "-march=rv64imac", "-mabi=lp64")),
    )
    .expect("write asm c")
    .expect("asm c");
    let c = std::fs::read_to_string(c_path).expect("read asm c");
    assert!(!c.contains("csrr 0, mcause"));
    assert!(!c.contains("csrc mip, msie"));
    assert!(c.contains("skipped Simple asm with unresolved operands"));
    assert!(c.contains("\"wfi\\n\""), "unbound lines in the same block must survive");
}
