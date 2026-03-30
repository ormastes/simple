//! Plugin manifest support for SFFI extern registration and dynamic loading.
//!
//! The manifest format is SDN and defaults to `~/.simple/plugins/manifest.sdn`.
//! A test or caller may override the path with `SIMPLE_PLUGIN_MANIFEST`.
//!
//! Expected shape:
//!
//! ```sdn
//! plugins:
//!     -
//!         name: regex
//!         library: /abs/path/libsimple_regex_ffi.so
//!         version: "0.1.0"
//!         functions: [rt_regex_new, rt_regex_destroy]
//! ```

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{LazyLock, Mutex};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PluginEntry {
    pub name: String,
    pub library: String,
    pub version: Option<String>,
    pub functions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PluginManifest {
    pub plugins: Vec<PluginEntry>,
    pub symbols: HashSet<String>,
    pub symbol_to_library: HashMap<String, String>,
}

#[derive(Debug, Clone, Default)]
struct PluginManifestCache {
    loaded: bool,
    manifest: PluginManifest,
    error: Option<String>,
}

static PLUGIN_MANIFEST_CACHE: LazyLock<Mutex<PluginManifestCache>> =
    LazyLock::new(|| Mutex::new(PluginManifestCache::default()));

pub const SIMPLE_PLUGIN_MANIFEST_ENV: &str = "SIMPLE_PLUGIN_MANIFEST";

pub fn plugin_manifest_path() -> Option<PathBuf> {
    if let Ok(path) = std::env::var(SIMPLE_PLUGIN_MANIFEST_ENV) {
        let trimmed = path.trim();
        if !trimmed.is_empty() {
            return Some(PathBuf::from(trimmed));
        }
    }

    let home = std::env::var("HOME").ok()?;
    if home.trim().is_empty() {
        return None;
    }
    Some(PathBuf::from(home).join(".simple").join("plugins").join("manifest.sdn"))
}

fn strip_quotes(value: &str) -> &str {
    let trimmed = value.trim();
    trimmed
        .strip_prefix('"')
        .and_then(|v| v.strip_suffix('"'))
        .unwrap_or(trimmed)
}

fn parse_functions_line(line: &str) -> Vec<String> {
    let Some(start) = line.find('[') else {
        return Vec::new();
    };
    let Some(end) = line.rfind(']') else {
        return Vec::new();
    };
    if end <= start {
        return Vec::new();
    }
    line[start + 1..end]
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(strip_quotes)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect()
}

fn finalize_plugin_entry(
    plugins: &mut Vec<PluginEntry>,
    name: &mut String,
    library: &mut String,
    version: &mut Option<String>,
    functions: &mut Vec<String>,
) -> Result<(), String> {
    if name.trim().is_empty() && library.trim().is_empty() && functions.is_empty() {
        return Ok(());
    }

    if name.trim().is_empty() {
        return Err("plugin entry missing non-empty 'name'".to_string());
    }
    if library.trim().is_empty() {
        return Err(format!("plugin '{}' missing non-empty 'library'", name.trim()));
    }
    if functions.is_empty() {
        return Err(format!("plugin '{}' must declare at least one function", name.trim()));
    }

    plugins.push(PluginEntry {
        name: name.trim().to_string(),
        library: library.trim().to_string(),
        version: version.take(),
        functions: std::mem::take(functions),
    });
    name.clear();
    library.clear();
    Ok(())
}

pub fn parse_plugin_manifest(path: &Path) -> Result<PluginManifest, String> {
    if !path.exists() {
        return Ok(PluginManifest::default());
    }

    let content = fs::read_to_string(path)
        .map_err(|e| format!("failed to read plugin manifest '{}': {}", path.display(), e))?;

    let mut plugins = Vec::new();
    let mut current_name = String::new();
    let mut current_library = String::new();
    let mut current_version = None;
    let mut current_functions = Vec::new();
    let mut in_plugins_section = false;

    for raw_line in content.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "plugins:" {
            in_plugins_section = true;
            continue;
        }
        if !in_plugins_section {
            continue;
        }
        if line == "-" {
            finalize_plugin_entry(
                &mut plugins,
                &mut current_name,
                &mut current_library,
                &mut current_version,
                &mut current_functions,
            )?;
            continue;
        }
        if let Some(value) = line.strip_prefix("name:") {
            current_name = strip_quotes(value).trim().to_string();
            continue;
        }
        if let Some(value) = line.strip_prefix("library:") {
            current_library = strip_quotes(value).trim().to_string();
            continue;
        }
        if let Some(value) = line.strip_prefix("version:") {
            let parsed = strip_quotes(value).trim().to_string();
            current_version = if parsed.is_empty() { None } else { Some(parsed) };
            continue;
        }
        if line.starts_with("functions:") {
            current_functions = parse_functions_line(line);
        }
    }

    finalize_plugin_entry(
        &mut plugins,
        &mut current_name,
        &mut current_library,
        &mut current_version,
        &mut current_functions,
    )?;

    let mut symbols = HashSet::new();
    let mut symbol_to_library = HashMap::new();

    for entry in &plugins {
        for symbol in &entry.functions {
            if !symbols.insert(symbol.clone()) {
                return Err(format!(
                    "plugin manifest '{}' declares duplicate extern symbol '{}'",
                    path.display(),
                    symbol
                ));
            }
            symbol_to_library.insert(symbol.clone(), entry.library.clone());
        }
    }

    Ok(PluginManifest {
        plugins,
        symbols,
        symbol_to_library,
    })
}

fn ensure_manifest_loaded() -> PluginManifestCache {
    let mut cache = PLUGIN_MANIFEST_CACHE.lock().expect("plugin manifest cache poisoned");
    if !cache.loaded {
        cache.loaded = true;
        match plugin_manifest_path() {
            Some(path) => match parse_plugin_manifest(&path) {
                Ok(manifest) => {
                    cache.manifest = manifest;
                    cache.error = None;
                }
                Err(error) => {
                    cache.manifest = PluginManifest::default();
                    cache.error = Some(error);
                }
            },
            None => {
                cache.manifest = PluginManifest::default();
                cache.error = None;
            }
        }
    }
    cache.clone()
}

pub fn registered_plugin_symbols() -> HashSet<String> {
    ensure_manifest_loaded().manifest.symbols
}

pub fn library_for_symbol(symbol: &str) -> Option<String> {
    ensure_manifest_loaded().manifest.symbol_to_library.get(symbol).cloned()
}

pub fn manifest_error() -> Option<String> {
    ensure_manifest_loaded().error
}

#[cfg(test)]
pub fn clear_plugin_manifest_cache() {
    let mut cache = PLUGIN_MANIFEST_CACHE.lock().expect("plugin manifest cache poisoned");
    *cache = PluginManifestCache::default();
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn parses_valid_manifest() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("manifest.sdn");
        fs::write(
            &path,
            r#"
plugins:
    -
        name: regex
        library: /tmp/libsimple_regex_ffi.so
        version: "0.1.0"
        functions: [rt_regex_new, rt_regex_destroy]
"#,
        )
        .unwrap();

        let manifest = parse_plugin_manifest(&path).unwrap();
        assert_eq!(manifest.plugins.len(), 1);
        assert!(manifest.symbols.contains("rt_regex_new"));
        assert_eq!(
            manifest.symbol_to_library.get("rt_regex_destroy"),
            Some(&"/tmp/libsimple_regex_ffi.so".to_string())
        );
    }

    #[test]
    fn rejects_duplicate_symbols() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("manifest.sdn");
        fs::write(
            &path,
            r#"
plugins:
    -
        name: regex
        library: /tmp/libsimple_regex_ffi.so
        functions: [rt_regex_new]
    -
        name: http
        library: /tmp/libsimple_http_ffi.so
        functions: [rt_regex_new]
"#,
        )
        .unwrap();

        let error = parse_plugin_manifest(&path).unwrap_err();
        assert!(error.contains("duplicate extern symbol"));
    }
}
