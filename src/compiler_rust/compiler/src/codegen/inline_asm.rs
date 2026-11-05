use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InlineAsmBlock {
    pub symbol: String,
    pub instructions: Vec<String>,
    pub volatile: bool,
    pub dialect: crate::hir::AsmDialect,
    pub naked: bool,
}

static INLINE_ASM_BLOCKS: OnceLock<Mutex<BTreeMap<String, InlineAsmBlock>>> = OnceLock::new();

fn registry() -> &'static Mutex<BTreeMap<String, InlineAsmBlock>> {
    INLINE_ASM_BLOCKS.get_or_init(|| Mutex::new(BTreeMap::new()))
}

fn hash_asm(instructions: &[String], volatile: bool, dialect: crate::hir::AsmDialect, naked: bool) -> u64 {
    let mut hash: u64 = 0xcbf29ce484222325;
    hash ^= u64::from(volatile as u8);
    hash = hash.wrapping_mul(0x100000001b3);
    // Preserve legacy non-naked symbols; a naked body needs a distinct sidecar.
    if naked {
        hash ^= 1;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    // Preserve legacy default symbols; explicit syntax changes artifact identity.
    if dialect != crate::hir::AsmDialect::Default {
        hash ^= match dialect {
            crate::hir::AsmDialect::Att => 1,
            crate::hir::AsmDialect::Intel => 2,
            crate::hir::AsmDialect::Default => unreachable!(),
        };
        hash = hash.wrapping_mul(0x100000001b3);
    }
    for instruction in instructions {
        for byte in instruction.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash ^= 0xff;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn register_inline_asm_impl(
    instructions: &[String],
    volatile: bool,
    dialect: crate::hir::AsmDialect,
    naked: bool,
) -> String {
    let hash = hash_asm(instructions, volatile, dialect, naked);
    let symbol = format!("__simple_asm_H{hash:016x}");
    let block = InlineAsmBlock {
        symbol: symbol.clone(),
        instructions: instructions.to_vec(),
        volatile,
        dialect,
        naked,
    };
    registry().lock().unwrap().entry(symbol.clone()).or_insert(block);
    symbol
}

pub fn register_inline_asm(instructions: &[String], volatile: bool, dialect: crate::hir::AsmDialect) -> String {
    register_inline_asm_impl(instructions, volatile, dialect, false)
}

pub fn register_naked_inline_asm(instructions: &[String], volatile: bool, dialect: crate::hir::AsmDialect) -> String {
    register_inline_asm_impl(instructions, volatile, dialect, true)
}

pub fn collected_inline_asm_blocks() -> Vec<InlineAsmBlock> {
    registry().lock().unwrap().values().cloned().collect()
}

pub fn clear_inline_asm_blocks() {
    registry().lock().unwrap().clear();
}
