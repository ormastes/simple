use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::UNIX_EPOCH;

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DepInfo {
    pub source: PathBuf,
    pub output: PathBuf,
    pub dependencies: Vec<PathBuf>,
    pub macros: Vec<String>,
    pub mtime: u64,
}

#[derive(Default, Serialize, Deserialize)]
pub struct BuildCache {
    entries: HashMap<PathBuf, DepInfo>,
}

const CACHE_FILE: &str = "target/simple_watch_cache.json";

impl BuildCache {
    pub fn load() -> Self {
        let path = PathBuf::from(CACHE_FILE);
        if let Ok(bytes) = fs::read(&path) {
            if let Ok(cache) = serde_json::from_slice(&bytes) {
                return cache;
            }
        }
        Self::default()
    }

    pub fn save(&self) {
        if let Some(parent) = Path::new(CACHE_FILE).parent() {
            let _ = fs::create_dir_all(parent);
        }
        if let Ok(bytes) = serde_json::to_vec_pretty(self) {
            let _ = fs::write(CACHE_FILE, bytes);
        }
    }

    pub fn update(&mut self, info: DepInfo) {
        self.entries.insert(info.source.clone(), info);
    }

    pub fn get(&self, source: &Path) -> Option<&DepInfo> {
        self.entries.get(source)
    }

    /// Find all sources that depend (directly) on the given path.
    pub fn dependents_of(&self, path: &Path) -> Vec<PathBuf> {
        let mut set = HashSet::new();
        for (src, info) in &self.entries {
            if info.dependencies.iter().any(|d| d == path) {
                set.insert(src.clone());
            }
        }
        set.into_iter().collect()
    }
}

pub fn analyze_source(path: &Path) -> std::io::Result<(Vec<PathBuf>, Vec<String>)> {
    let content = fs::read_to_string(path)?;
    Ok(analyze_source_str(path, &content))
}

pub fn analyze_source_str(base: &Path, content: &str) -> (Vec<PathBuf>, Vec<String>) {
    let mut deps = Vec::new();
    let mut macros = Vec::new();

    for line in content.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("import ") {
            if let Some(token) = rest.split_whitespace().next() {
                let mut path = PathBuf::from(token);
                if path.extension().is_none() {
                    path.set_extension("spl");
                }
                // Resolve relative to the source file directory.
                if path.is_relative() {
                    if let Some(parent) = base.parent() {
                        path = parent.join(path);
                    }
                }
                deps.push(path);
            }
        } else if let Some(rest) = trimmed.strip_prefix("macro ") {
            if let Some(raw) = rest.split_whitespace().next() {
                let name = raw.split(|c| c == '(' || c == '=').next().unwrap_or(raw).trim();
                if !name.is_empty() {
                    macros.push(name.to_string());
                }
            }
        }
    }

    (deps, macros)
}

pub fn current_mtime(path: &Path) -> u64 {
    fs::metadata(path)
        .and_then(|m| m.modified())
        .ok()
        .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
        .map(|d| d.as_secs())
        .unwrap_or(0)
}
