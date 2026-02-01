// String interner for deduplicating strings
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StringInterner {
    strings: HashMap<String, u32>,
    reverse: Vec<String>,
}

impl StringInterner {
    pub fn new() -> Self {
        Self {
            strings: HashMap::new(),
            reverse: Vec::new(),
        }
    }

    pub fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.strings.get(s) {
            return id;
        }
        let id = self.reverse.len() as u32;
        self.strings.insert(s.to_string(), id);
        self.reverse.push(s.to_string());
        id
    }

    pub fn get(&self, id: u32) -> Option<&str> {
        self.reverse.get(id as usize).map(|s| s.as_str())
    }

    pub fn get_or_empty(&self, id: u32) -> &str {
        self.reverse.get(id as usize).map(|s| s.as_str()).unwrap_or("")
    }

    pub fn lookup(&self, s: &str) -> Option<u32> {
        self.strings.get(s).copied()
    }

    pub fn len(&self) -> usize {
        self.reverse.len()
    }

    pub fn is_empty(&self) -> bool {
        self.reverse.is_empty()
    }

    /// Serialize to SDN rows: `[id, value]`
    pub fn to_sdn_rows(&self) -> Vec<(u32, &str)> {
        self.reverse.iter().enumerate().map(|(id, s)| (id as u32, s.as_str())).collect()
    }
}

impl Default for StringInterner {
    fn default() -> Self {
        Self::new()
    }
}
