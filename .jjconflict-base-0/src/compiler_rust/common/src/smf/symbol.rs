use std::collections::HashMap;

use tracing::{trace, warn};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LayoutPhaseFlag {
    Startup = 0,
    FirstFrame = 1,
    Steady = 2,
    Cold = 3,
}

impl LayoutPhaseFlag {
    pub fn from_flags(flags: u8) -> Self {
        match flags & 0x03 {
            0 => LayoutPhaseFlag::Startup,
            1 => LayoutPhaseFlag::FirstFrame,
            2 => LayoutPhaseFlag::Steady,
            _ => LayoutPhaseFlag::Cold,
        }
    }

    pub fn to_flags(self) -> u8 {
        self as u8
    }
}

pub mod symbol_flags {
    pub const LAYOUT_PHASE_MASK: u8 = 0x03;
    pub const EVENT_LOOP_ANCHOR: u8 = 0x04;
    pub const LAYOUT_PINNED: u8 = 0x08;
    pub const GENERIC_TEMPLATE: u8 = 0x10;
    pub const SPECIALIZED: u8 = 0x20;
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfSymbol {
    pub name_offset: u32,
    pub name_hash: u32,
    pub sym_type: SymbolType,
    pub binding: SymbolBinding,
    pub visibility: u8,
    pub flags: u8,
    pub value: u64,
    pub size: u64,
    pub type_id: u32,
    pub version: u32,
    pub template_param_count: u8,
    pub reserved: [u8; 3],
    pub template_offset: u64,
}

impl SmfSymbol {
    pub fn layout_phase(&self) -> LayoutPhaseFlag {
        LayoutPhaseFlag::from_flags(self.flags)
    }

    pub fn is_event_loop_anchor(&self) -> bool {
        self.flags & symbol_flags::EVENT_LOOP_ANCHOR != 0
    }

    pub fn is_layout_pinned(&self) -> bool {
        self.flags & symbol_flags::LAYOUT_PINNED != 0
    }

    pub fn is_generic_template(&self) -> bool {
        self.flags & symbol_flags::GENERIC_TEMPLATE != 0
    }

    pub fn is_specialized(&self) -> bool {
        self.flags & symbol_flags::SPECIALIZED != 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SymbolType {
    None = 0,
    Function = 1,
    Data = 2,
    Type = 3,
    Trait = 4,
    Actor = 5,
    Constant = 6,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SymbolBinding {
    Local = 0,
    Global = 1,
    Weak = 2,
}

pub struct SymbolTable {
    pub symbols: Vec<SmfSymbol>,
    string_table: Vec<u8>,
    hash_table: HashMap<u32, Vec<usize>>,
}

impl SymbolTable {
    pub fn new(symbols: Vec<SmfSymbol>, string_table: Vec<u8>) -> Self {
        trace!(
            symbol_count = symbols.len(),
            string_table_size = string_table.len(),
            "Building symbol hash table"
        );

        let mut hash_table = HashMap::new();
        for (i, sym) in symbols.iter().enumerate() {
            hash_table.entry(sym.name_hash).or_insert_with(Vec::new).push(i);
        }

        trace!(unique_hashes = hash_table.len(), "Symbol hash table built");

        Self {
            symbols,
            string_table,
            hash_table,
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&SmfSymbol> {
        let hash = hash_name(name);
        let result = self.hash_table.get(&hash).and_then(|indices| {
            indices.iter().find_map(|&i| {
                let sym = &self.symbols[i];
                if self.symbol_name(sym) == name {
                    Some(sym)
                } else {
                    None
                }
            })
        });

        if result.is_none() {
            trace!(name, hash, "Symbol not found");
        }

        result
    }

    pub fn symbol_name(&self, sym: &SmfSymbol) -> &str {
        let start = sym.name_offset as usize;
        if start >= self.string_table.len() {
            warn!(
                name_offset = start,
                string_table_len = self.string_table.len(),
                "Symbol name offset exceeds string table bounds"
            );
            return "";
        }

        let end = self
            .string_table
            .get(start..)
            .and_then(|rest| rest.iter().position(|&b| b == 0).map(|i| start + i))
            .unwrap_or(self.string_table.len());

        if end > self.string_table.len() {
            warn!(
                start,
                end,
                string_table_len = self.string_table.len(),
                "Symbol name end exceeds string table bounds"
            );
            return "";
        }

        match std::str::from_utf8(&self.string_table[start..end]) {
            Ok(name) => name,
            Err(e) => {
                warn!(start, end, error = %e, "Invalid UTF-8 in symbol name");
                ""
            }
        }
    }

    pub fn exports(&self) -> impl Iterator<Item = &SmfSymbol> {
        self.symbols.iter().filter(|s| s.binding == SymbolBinding::Global)
    }
}

pub fn hash_name(name: &str) -> u32 {
    const FNV_OFFSET: u32 = 2166136261;
    const FNV_PRIME: u32 = 16777619;

    let mut hash = FNV_OFFSET;
    for byte in name.bytes() {
        hash ^= byte as u32;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}
