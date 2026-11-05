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
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
            instructions: vec!["in eax, dx".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            dialect: crate::hir::AsmDialect::Default,
            instructions: vec!["mov cr3, pd".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            dialect: crate::hir::AsmDialect::Default,
            instructions: vec!["out dx, eax".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            dialect: crate::hir::AsmDialect::Default,
            instructions: vec!["invlpg [addr]".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        // A genuinely riscv block must survive the same filter, so the test
        // cannot pass by emitting nothing at all.
        block.instructions.push(MirInst::InlineAsm {
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
            instructions: vec!["csrw mtvec, t0".to_string()],
            volatile: true,
            constraints: String::new(),
            inputs: vec![],
            outputs: vec![],
        });
        block.instructions.push(MirInst::InlineAsm {
            dialect: crate::hir::AsmDialect::Default,
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
            dialect: crate::hir::AsmDialect::Default,
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

#[test]
fn inline_asm_dialect_defaults_and_conflicts() {
    use crate::hir::AsmDialect;
    assert_eq!(AsmDialect::from_options([]), Ok(AsmDialect::Default));
    assert_eq!(AsmDialect::from_options(["nostack", "intel_syntax"]), Ok(AsmDialect::Intel));
    assert!(AsmDialect::from_options(["att_syntax", "intel_syntax"]).is_err());
    assert!(AsmDialect::from_options(["intel_syntax", "att_syntax"]).is_err());
}

#[test]
fn hir_rejects_conflicting_explicit_asm_syntax() {
    let source = "fn main() -> i64:\n    asm volatile(\"nop\", options(att_syntax, intel_syntax))\n    return 0\n";
    let mut parser = simple_parser::Parser::new(source);
    let ast = parser.parse().expect("parse conflict");
    let mut lowerer = Lowerer::new();
    let error = lowerer.lower_module(&ast).expect_err("conflicting syntax must fail");
    assert!(error.to_string().contains("E-ASM-DIALECT"));
}

#[test]
fn inline_asm_explicit_dialect_survives_hir_and_mir() {
    use crate::hir::AsmDialect;
    for (option, expected) in [("", AsmDialect::Default), (", options(intel_syntax)", AsmDialect::Intel)] {
        let source = format!("fn main() -> i64:\n    asm volatile(\"nop\"{option})\n    return 0\n");
        let mut parser = simple_parser::Parser::new(&source);
        let ast = parser.parse().expect("parse dialect");
        let mut lowerer = Lowerer::new();
        lowerer.set_lenient_types(true);
        let hir = lowerer.lower_module(&ast).expect("lower dialect");
        assert!(hir.functions.iter().flat_map(|f| &f.body).any(|stmt|
            matches!(stmt, HirStmt::InlineAsm { dialect, .. } if *dialect == expected)));
        let mir = crate::mir::lower_to_mir(&hir).expect("MIR dialect");
        assert!(mir.functions.iter().flat_map(|f| &f.blocks).flat_map(|b| &b.instructions).any(|inst|
            matches!(inst, MirInst::InlineAsm { dialect, .. } if *dialect == expected)));
    }
}

#[test]
fn sidecar_dialect_identity_and_target_admission() {
    use crate::hir::AsmDialect;
    use crate::codegen::inline_asm::{clear_inline_asm_blocks, register_inline_asm};
    use crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target;
    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    clear_inline_asm_blocks();
    let instructions = vec!["nop".to_string()];
    let default = register_inline_asm(&instructions, true, AsmDialect::Default);
    let att = register_inline_asm(&instructions, true, AsmDialect::Att);
    let intel = register_inline_asm(&instructions, true, AsmDialect::Intel);
    assert_ne!(default, att);
    assert_ne!(default, intel);
    assert_ne!(att, intel);
    assert_eq!(intel, register_inline_asm(&instructions, true, AsmDialect::Intel));
    clear_inline_asm_blocks();
    for (dialect, expects_intel) in [(AsmDialect::Default, true), (AsmDialect::Att, false), (AsmDialect::Intel, true)] {
        clear_inline_asm_blocks();
        register_inline_asm(&instructions, true, dialect);
        let dir = tempfile::tempdir().expect("tempdir");
        let path = write_inline_asm_c_for_target(dir.path(), Some(("x86_64-unknown-none", "", "")))
            .expect("dialect admitted").expect("sidecar");
        let source = std::fs::read_to_string(path).expect("source");
        assert_eq!(source.contains(".intel_syntax noprefix"), expects_intel);
        assert_eq!(source.contains(".att_syntax prefix"), expects_intel);
        assert!(source.contains("nop"));
    }
    let dir = tempfile::tempdir().expect("tempdir");
    assert!(write_inline_asm_c_for_target(dir.path(), Some(("aarch64-unknown-none", "", ""))).is_err());
    assert!(!dir.path().join("simple_asm_blocks.c").exists());
    // Preserve the existing whole-closure foreign-architecture filter. This
    // source-generation assertion is not ARM or x86 native qualification.
    clear_inline_asm_blocks();
    register_inline_asm(&["out dx, al".to_string()], true, AsmDialect::Intel);
    let foreign = tempfile::tempdir().expect("foreign tempdir");
    let path = write_inline_asm_c_for_target(foreign.path(), Some(("aarch64-unknown-none", "", "")))
        .expect("foreign block filtered").expect("sidecar");
    assert!(!std::fs::read_to_string(path).expect("foreign source").contains("out dx, al"));
    clear_inline_asm_blocks();
}

#[test]
fn naked_sidecar_attribute_does_not_change_regular_asm() {
    use crate::codegen::inline_asm::{clear_inline_asm_blocks, register_inline_asm, register_naked_inline_asm};
    use crate::hir::AsmDialect;
    use crate::pipeline::native_project::inline_asm_emit::write_inline_asm_c_for_target;

    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    clear_inline_asm_blocks();
    let instructions = vec!["nop".to_string()];
    let regular = register_inline_asm(&instructions, true, AsmDialect::Default);
    let naked = register_naked_inline_asm(&instructions, true, AsmDialect::Default);
    assert_ne!(regular, naked, "naked and regular bodies must not share a sidecar symbol");
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_inline_asm_c_for_target(dir.path(), Some(("x86_64-unknown-none", "", "")))
        .expect("write asm")
        .expect("sidecar");
    let source = std::fs::read_to_string(path).expect("read asm");
    assert!(source.contains(&format!("__attribute__((used)) void {regular}(void)")));
    assert!(source.contains(&format!("__attribute__((used, naked)) void {naked}(void)")));
    clear_inline_asm_blocks();
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn disassemble_symbol(object: &std::path::Path, symbol: &str) -> String {
    let output = std::process::Command::new("objdump")
        .arg("-d")
        .arg(format!("--disassemble={symbol}"))
        .arg(object)
        .output()
        .expect("run objdump");
    assert!(output.status.success(), "objdump {symbol}: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout).expect("objdump utf8")
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn first_instruction(disassembly: &str) -> &str {
    disassembly
        .lines()
        .find(|line| line.contains(":\t"))
        .and_then(|line| line.split('\t').nth(2))
        .map(str::trim)
        .unwrap_or_else(|| panic!("no instruction in disassembly:\n{disassembly}"))
}

/// Reproduces both SimpleOS mutex failures from
/// `naked_asm_lowering_miscompiles_simpleos_mutex_2026-09-01`: a sidecar frame
/// prologue and a wrapper call followed by ud2. Also executes the resulting
/// objects so the CAS transitions and CPU-ID return path are checked, not just
/// the generated C source.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn naked_simpleos_mutex_cas_cpu_id_disassembly_and_execution() {
    use crate::hir::{AsmDialect, TypeId};
    use crate::mir::{BlockId, LocalKind, MirFunction, MirInst, MirLocal, MirModule, Terminator};
    use simple_parser::ast::Visibility;

    fn naked_function(name: &str, param_count: usize, instructions: &[&str]) -> MirFunction {
        let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
        func.attributes.push("naked".to_string());
        for index in 0..param_count {
            func.params.push(MirLocal {
                name: format!("arg{index}"),
                ty: TypeId::I64,
                kind: LocalKind::Parameter,
                is_ghost: false,
            });
        }
        func.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::InlineAsm {
            dialect: AsmDialect::Default,
            instructions: instructions.iter().map(|instruction| instruction.to_string()).collect(),
            volatile: true,
            constraints: "~{memory}".to_string(),
            inputs: vec![],
            outputs: vec![],
        });
        func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Unreachable;
        func
    }

    let _guard = inline_asm_test_lock().lock().expect("inline asm test lock");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
    let mut module = MirModule::new();
    module.functions.push(naked_function(
        "_mutex_word_cas",
        3,
        &[
            "mov eax, esi",
            "lock cmpxchg dword ptr [rdi], edx",
            "sete al",
            "movzx eax, al",
            "ret",
        ],
    ));
    module.functions.push(naked_function(
        "_mutex_cpu_id",
        0,
        &[
            "push rbx",
            "xor eax, eax",
            "cpuid",
            "cmp eax, 0xb",
            "jb .Lsimpleos_mutex_x64_legacy_apic",
            "mov eax, 0xb",
            "xor ecx, ecx",
            "cpuid",
            "test ebx, ebx",
            "jz .Lsimpleos_mutex_x64_legacy_apic",
            "mov eax, edx",
            "pop rbx",
            "ret",
            ".Lsimpleos_mutex_x64_legacy_apic:",
            "mov eax, 1",
            "cpuid",
            "shr ebx, 24",
            "movzx eax, bl",
            "pop rbx",
            "ret",
        ],
    ));
    let object = crate::codegen::Codegen::new()
        .expect("codegen")
        .compile_module(&module)
        .expect("compile naked mutex module");
    let dir = tempfile::tempdir().expect("tempdir");
    let wrappers = dir.path().join("mutex_wrappers.o");
    std::fs::write(&wrappers, object).expect("write wrappers");
    let asm_object = crate::pipeline::native_project::inline_asm_emit::compile_inline_asm_c(
        dir.path(),
        Some(("x86_64-unknown-none", "", "")),
    )
    .expect("compile naked sidecar")
    .expect("sidecar object");

    let blocks = crate::codegen::inline_asm::collected_inline_asm_blocks();
    assert_eq!(blocks.len(), 2);
    assert!(blocks.iter().all(|block| block.naked));
    let cas_symbol = &blocks
        .iter()
        .find(|block| block.instructions.iter().any(|instruction| instruction.contains("cmpxchg")))
        .expect("CAS block")
        .symbol;
    let cpu_symbol = &blocks
        .iter()
        .find(|block| block.instructions.iter().any(|instruction| instruction == "cpuid"))
        .expect("CPU-ID block")
        .symbol;

    let cas_thunk = disassemble_symbol(&asm_object, cas_symbol);
    assert!(first_instruction(&cas_thunk).starts_with("mov    %esi,%eax"), "{cas_thunk}");
    assert!(cas_thunk.contains("lock cmpxchg %edx,(%rdi)"), "{cas_thunk}");
    assert!(cas_thunk.contains("sete   %al") && cas_thunk.contains("movzbl %al,%eax"), "{cas_thunk}");
    assert!(!cas_thunk.contains("%rbp"), "naked CAS sidecar gained a frame:\n{cas_thunk}");
    let cpu_thunk = disassemble_symbol(&asm_object, cpu_symbol);
    assert!(first_instruction(&cpu_thunk).starts_with("push   %rbx"), "{cpu_thunk}");
    assert_eq!(cpu_thunk.matches("cpuid").count(), 3, "{cpu_thunk}");
    assert!(cpu_thunk.contains("shr    $0x18,%ebx"), "{cpu_thunk}");
    assert!(!cpu_thunk.contains("%rbp"), "naked CPU-ID sidecar gained a frame:\n{cpu_thunk}");

    for wrapper in ["_mutex_word_cas", "_mutex_cpu_id"] {
        let disassembly = disassemble_symbol(&wrappers, wrapper);
        assert!(disassembly.contains("call"), "wrapper does not call its thunk:\n{disassembly}");
        assert!(disassembly.contains("ret"), "wrapper does not propagate the return:\n{disassembly}");
        assert!(!disassembly.contains("ud2"), "wrapper traps after its call:\n{disassembly}");
    }

    let harness = dir.path().join("mutex_harness.c");
    std::fs::write(
        &harness,
        r#"#include <stdint.h>
extern uint64_t _mutex_word_cas(uint64_t addr, uint32_t expected, uint32_t desired);
extern uint64_t _mutex_cpu_id(void);
int main(void) {
    uint32_t word = 0;
    if (_mutex_word_cas((uint64_t)(uintptr_t)&word, 0, 42) != 1 || word != 42) return 1;
    if (_mutex_word_cas((uint64_t)(uintptr_t)&word, 0, 99) != 0 || word != 42) return 2;
    if (_mutex_word_cas((uint64_t)(uintptr_t)&word, 42, 0) != 1 || word != 0) return 3;
    (void)_mutex_cpu_id();
    return 0;
}
"#,
    )
    .expect("write harness");
    let executable = dir.path().join("mutex_harness");
    let link = std::process::Command::new("clang")
        .arg("-no-pie")
        .arg(&harness)
        .arg(&wrappers)
        .arg(&asm_object)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("link mutex harness");
    assert!(link.status.success(), "link mutex harness: {}", String::from_utf8_lossy(&link.stderr));
    let run = std::process::Command::new(&executable).output().expect("run mutex harness");
    assert!(run.status.success(), "mutex harness failed: {run:?}");
    crate::codegen::inline_asm::clear_inline_asm_blocks();
}
