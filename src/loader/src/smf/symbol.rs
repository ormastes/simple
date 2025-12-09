use std::collections::HashMap;

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

/// Fast symbol lookup using hash table
pub struct SymbolTable {
    pub symbols: Vec<SmfSymbol>,
    string_table: Vec<u8>,
    hash_table: HashMap<u32, Vec<usize>>,
}

impl SymbolTable {
    pub fn new(symbols: Vec<SmfSymbol>, string_table: Vec<u8>) -> Self {
        let mut hash_table = HashMap::new();

        for (i, sym) in symbols.iter().enumerate() {
            hash_table.entry(sym.name_hash).or_insert_with(Vec::new).push(i);
        }

        Self {
            symbols,
            string_table,
            hash_table,
        }
    }

    /// O(1) average lookup by name
    pub fn lookup(&self, name: &str) -> Option<&SmfSymbol> {
        let hash = hash_name(name);

        self.hash_table.get(&hash).and_then(|indices| {
            indices.iter().find_map(|&i| {
                let sym = &self.symbols[i];
                if self.symbol_name(sym) == name {
                    Some(sym)
                } else {
                    None
                }
            })
        })
    }

    pub fn symbol_name(&self, sym: &SmfSymbol) -> &str {
        let start = sym.name_offset as usize;
        let end = self
            .string_table
            .get(start..)
            .and_then(|rest| rest.iter().position(|&b| b == 0).map(|i| start + i))
            .unwrap_or(self.string_table.len());

        std::str::from_utf8(&self.string_table[start..end]).unwrap_or("")
    }

    /// Get all exported symbols
    pub fn exports(&self) -> impl Iterator<Item = &SmfSymbol> {
        self.symbols.iter().filter(|s| s.binding == SymbolBinding::Global)
    }
}

/// FNV-1a hash for symbol names
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
