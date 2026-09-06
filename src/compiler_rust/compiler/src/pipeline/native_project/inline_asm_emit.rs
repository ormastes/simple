use std::path::{Path, PathBuf};

use super::tools::find_c_compiler;

fn escape_c_asm_string(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => {}
            '\t' => out.push_str("\\t"),
            '%' => out.push_str("%%"),
            _ => out.push(ch),
        }
    }
    out
}

fn target_uses_x86_intel_asm(target: Option<(&str, &str, &str)>) -> bool {
    target
        .map(|(triple, _, _)| triple.contains("x86_64") || triple.starts_with("i386"))
        .unwrap_or(false)
}

/// Architecture families the emitter can recognise from an instruction's
/// mnemonic. `Neutral` means "no evidence either way" — a directive, a label,
/// a comment, or a mnemonic several families share (`nop`, `ret`, `j`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AsmArch {
    X86,
    Riscv,
    Arm,
    Neutral,
}

fn target_asm_arch(triple: &str) -> AsmArch {
    if triple.contains("x86_64") || triple.starts_with("i386") || triple.starts_with("i686") {
        AsmArch::X86
    } else if triple.starts_with("riscv") {
        AsmArch::Riscv
    } else if triple.starts_with("aarch64") || triple.starts_with("arm") || triple.starts_with("thumb") {
        AsmArch::Arm
    } else {
        AsmArch::Neutral
    }
}

/// Classify one instruction line. Only UNMISTAKABLE evidence counts: a line the
/// emitter cannot attribute stays `Neutral` and is therefore kept for every
/// target, so this filter can never silently drop a block it merely failed to
/// understand.
fn instruction_asm_arch(instruction: &str) -> AsmArch {
    let text = instruction.trim_start();
    let mnemonic = text.split(|c: char| c.is_whitespace() || c == ',').next().unwrap_or("");

    // x86 / x86_64
    const X86_MNEMONICS: &[&str] = &[
        "in", "out", "inb", "outb", "inw", "outw", "inl", "outl", "invlpg", "hlt", "cli", "sti",
        "iret", "iretq", "lgdt", "lidt", "lldt", "ltr", "cpuid", "rdmsr", "wrmsr", "rdtsc",
        "sysret", "sysexit", "swapgs", "pushfq", "popfq", "xchg", "movq", "movl", "movw", "movb",
        "leaq", "lea", "int3", "ud2", "wbinvd", "clts", "stac", "clac", "sgdt", "sidt", "verr",
    ];
    if X86_MNEMONICS.contains(&mnemonic) || text.starts_with(".intel_syntax") || text.starts_with(".att_syntax") {
        return AsmArch::X86;
    }
    // `mov` is shared between x86 and ARM, but it is NOT a RISC-V mnemonic
    // (RISC-V spells the same thing `mv`), and the only two targets this
    // predicate can reject for are x86 and RISC-V — `compile_inline_asm_c`
    // bails out of the C sidecar entirely for aarch64/arm before reaching
    // here. Classifying it as x86 is therefore decisive where it matters and
    // unreachable where it would be wrong.
    if mnemonic == "mov" || mnemonic == "movzx" || mnemonic == "movsx" {
        return AsmArch::X86;
    }

    // RISC-V
    const RISCV_MNEMONICS: &[&str] = &[
        "mv", "addi", "sw", "lw", "sd", "ld", "li", "la", "sret", "mret", "ecall", "ebreak", "wfi", "auipc",
    ];
    if RISCV_MNEMONICS.contains(&mnemonic)
        || mnemonic.starts_with("csrr")
        || mnemonic.starts_with("csrw")
        || mnemonic.starts_with("csrs")
        || mnemonic.starts_with("csrc")
        || mnemonic.starts_with("sfence.vma")
        || mnemonic.starts_with("fence.i")
        || text.starts_with(".option ")
    {
        return AsmArch::Riscv;
    }

    // ARM / AArch64
    const ARM_MNEMONICS: &[&str] = &[
        "mrs", "msr", "dmb", "dsb", "isb", "wfe", "eret", "ldp", "stp", "ldr", "str", "bl", "blr",
        "cbz", "cbnz", "svc", "hvc", "smc", "cpsie", "cpsid", "adrp",
    ];
    if ARM_MNEMONICS.contains(&mnemonic) {
        return AsmArch::Arm;
    }

    AsmArch::Neutral
}

/// Decide whether a collected block belongs in this target's translation unit.
///
/// Full entry-closure discovery visits architecture-specific modules whose
/// `@cfg` functions are not selected for this target, and the inline-asm
/// registry is PROCESS-GLOBAL, so every arch's blocks are present here
/// regardless of target. This filter is the designed mechanism for that.
///
/// It used to have only the x86 arm — a riscv64 or aarch64 build emitted every
/// x86 block into its own TU, and `in eax, dx` / `mov cr3, pd` / `invlpg` went
/// to the riscv64 assembler (8 of the 18 errors in
/// `doc/08_tracking/bug/rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md`).
/// It is now symmetric: a block is rejected when it carries UNMISTAKABLE
/// evidence of a family other than the target's. Blocks with no such evidence
/// are kept, exactly as before.
fn block_matches_target(instructions: &[String], target: Option<(&str, &str, &str)>) -> bool {
    let Some((triple, _, _)) = target else {
        return true;
    };
    let want = target_asm_arch(triple);
    if want == AsmArch::Neutral {
        return true;
    }
    !instructions.iter().any(|instruction| {
        let found = instruction_asm_arch(instruction);
        found != AsmArch::Neutral && found != want
    })
}

fn has_unresolved_simple_operand(instruction: &str) -> bool {
    let directive = instruction
        .split_once('=')
        .map_or(instruction, |(_, value)| value)
        .trim_start();
    let is_simple_operand_directive = ["in", "out", "inout", "lateout", "clobber", "clobber_abi", "options"]
        .iter()
        .any(|keyword| {
            directive
                .strip_prefix(keyword)
                .is_some_and(|rest| rest.trim_start().starts_with('('))
        });

    // `$N` is the LLVM operand reference the MIR lowering rewrites `{name}`
    // into (mir/asm_operands.rs); the C sidecar cannot bind operands, so such
    // a line is skipped here exactly like the `{name}` form was.
    let has_llvm_operand_ref = instruction
        .char_indices()
        .any(|(i, c)| c == '$' && instruction[i + 1..].starts_with(|d: char| d.is_ascii_digit()));

    instruction.contains('{')
        || instruction.contains('}')
        || has_llvm_operand_ref
        || is_simple_operand_directive
        // Unresolved Simple asm operands leak as the Rust `{:?}` of the AST
        // operand node, e.g. `li t0, Identifier("mstatus_mie")` or
        // `csrr Integer(0), mhartid` (seen in the riscv/riscv32 baremetal startup
        // blocks). These are never valid assembler tokens, and the host bootstrap
        // binary never executes those baremetal blocks, so skip them instead of
        // emitting invalid asm that fails the clang assemble step.
        || instruction.contains("Identifier(")
        || instruction.contains("Integer(")
}

pub(crate) fn write_inline_asm_c_for_target(
    temp_dir: &Path,
    target: Option<(&str, &str, &str)>,
) -> Result<Option<PathBuf>, String> {
    let blocks = crate::codegen::inline_asm::collected_inline_asm_blocks();
    if blocks.is_empty() {
        return Ok(None);
    }

    let use_intel_syntax = target_uses_x86_intel_asm(target);
    let path = temp_dir.join("simple_asm_blocks.c");
    let mut code = String::from("/* Auto-generated Simple raw asm blocks. */\n\n");
    for block in blocks {
        if !block_matches_target(&block.instructions, target) {
            continue;
        }
        code.push_str(&format!("__attribute__((used)) void {}(void) {{\n", block.symbol));
        code.push_str("    __asm__ volatile (\n");
        if use_intel_syntax {
            code.push_str("        \".intel_syntax noprefix\\n\"\n");
        }
        for instruction in &block.instructions {
            if has_unresolved_simple_operand(instruction) {
                code.push_str("        \"# skipped Simple asm with unresolved operands\\n\"\n");
            } else {
                code.push_str(&format!("        \"{}\\n\"\n", escape_c_asm_string(instruction)));
            }
        }
        if use_intel_syntax {
            code.push_str("        \".att_syntax prefix\\n\"\n");
        }
        code.push_str("        ::: \"memory\"\n");
        code.push_str("    );\n");
        code.push_str("}\n\n");
    }
    std::fs::write(&path, code).map_err(|e| format!("write inline asm C: {e}"))?;
    Ok(Some(path))
}

pub(crate) fn write_inline_asm_c(temp_dir: &Path) -> Result<Option<PathBuf>, String> {
    write_inline_asm_c_for_target(temp_dir, None)
}

pub(crate) fn compile_inline_asm_c(
    temp_dir: &Path,
    target: Option<(&str, &str, &str)>,
) -> Result<Option<PathBuf>, String> {
    if let Some((triple, _, _)) = target {
        if (triple.starts_with("aarch64") || triple.starts_with("arm"))
            && !crate::codegen::inline_asm::collected_inline_asm_blocks().is_empty()
        {
            return Ok(None);
        }
    }
    let Some(c_path) = write_inline_asm_c_for_target(temp_dir, target)? else {
        return Ok(None);
    };
    let out = temp_dir.join("simple_asm_blocks.o");
    let cc = find_c_compiler();
    let mut cmd = std::process::Command::new(&cc);
    cmd.arg("-c").arg("-o").arg(&out).arg(&c_path);
    if let Some((triple, march, mabi)) = target {
        cmd.arg(format!("--target={triple}"))
            .arg("-nostdlib")
            .arg("-ffreestanding")
            .arg("-fno-pic")
            .arg("-fno-pie");
        if !march.is_empty() {
            cmd.arg(march).arg(mabi);
            if triple.starts_with("riscv") {
                cmd.arg("-mcmodel=medany");
            }
        }
        if triple.contains("x86_64") {
            cmd.arg("-mno-red-zone");
        }
    } else {
        cmd.arg("-ffunction-sections").arg("-fdata-sections");
    }

    let output = cmd.output().map_err(|e| format!("compile inline asm C ({cc}): {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if target.is_none() {
            eprintln!(
                "[WARN] inline asm compilation failed (host target) — skipping asm object. \
                 This is expected when full-scan pulls in wrong-arch asm blocks.\n  {}",
                stderr.lines().take(3).collect::<Vec<_>>().join("\n  ")
            );
            return Ok(None);
        }
        return Err(format!("compile inline asm C failed: {}", stderr));
    }
    Ok(Some(out))
}
