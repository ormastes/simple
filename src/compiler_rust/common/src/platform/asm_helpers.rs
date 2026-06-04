//! Architecture-specific assembly helpers.
//!
//! Provides ret/jump instructions and tagged-nil return sequences
//! per CPU architecture, used by the stub generator and native backend.

use crate::target::{Target, TargetArch};

/// Get the architecture-appropriate `ret` instruction for inline asm stubs.
pub fn asm_ret_instruction(target: &Target) -> &'static str {
    match target.arch {
        TargetArch::X86_64 | TargetArch::X86 => "ret",
        TargetArch::Aarch64 => "ret", // uses x30 (link register)
        TargetArch::Arm => "bx lr",
        TargetArch::Riscv64 | TargetArch::Riscv32 => "ret", // pseudo for jalr x0, ra, 0
        _ => "ret",                                         // fallback
    }
}

/// Get the assembly sequence that returns tagged nil (value 3).
///
/// Simple's runtime uses tag bits: 0 is not a valid nil, 3 is tagged nil.
/// This is used by stub functions for unresolved symbols.
pub fn asm_ret_nil(target: &Target) -> &'static str {
    match target.arch {
        TargetArch::Aarch64 => "mov x0, #3\n  ret",
        TargetArch::X86_64 => "movq $3, %rax\n  retq",
        TargetArch::X86 => "movl $3, %eax\n  ret",
        TargetArch::Arm => "mov r0, #3\n  bx lr",
        TargetArch::Riscv64 | TargetArch::Riscv32 => "li a0, 3\n  ret",
        _ => "ret", // fallback
    }
}

/// Get the jump instruction prefix for the target architecture.
///
/// Used for builtin trampolines (e.g., `___builtin_X` → `_X`).
pub fn asm_jmp_instruction(target: &Target) -> &'static str {
    match target.arch {
        TargetArch::Aarch64 | TargetArch::Arm => "b",
        TargetArch::X86_64 | TargetArch::X86 => "jmp",
        TargetArch::Riscv64 | TargetArch::Riscv32 => "j",
        _ => "jmp",
    }
}
