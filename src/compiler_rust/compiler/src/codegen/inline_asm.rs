use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InlineAsmBlock {
    pub symbol: String,
    pub instructions: Vec<String>,
    pub volatile: bool,
}

static INLINE_ASM_BLOCKS: OnceLock<Mutex<BTreeMap<String, InlineAsmBlock>>> = OnceLock::new();

fn registry() -> &'static Mutex<BTreeMap<String, InlineAsmBlock>> {
    INLINE_ASM_BLOCKS.get_or_init(|| Mutex::new(BTreeMap::new()))
}

fn hash_asm(instructions: &[String], volatile: bool) -> u64 {
    let mut hash: u64 = 0xcbf29ce484222325;
    hash ^= u64::from(volatile as u8);
    hash = hash.wrapping_mul(0x100000001b3);
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

pub fn register_inline_asm(instructions: &[String], volatile: bool) -> String {
    let hash = hash_asm(instructions, volatile);
    let symbol = format!("__simple_asm_H{hash:016x}");
    let block = InlineAsmBlock {
        symbol: symbol.clone(),
        instructions: instructions.to_vec(),
        volatile,
    };
    registry().lock().unwrap().entry(symbol.clone()).or_insert(block);
    symbol
}

pub fn collected_inline_asm_blocks() -> Vec<InlineAsmBlock> {
    registry().lock().unwrap().values().cloned().collect()
}

pub fn clear_inline_asm_blocks() {
    registry().lock().unwrap().clear();
}
