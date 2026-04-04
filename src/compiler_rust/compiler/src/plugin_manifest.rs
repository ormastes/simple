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
pub struct PluginMethodEntry {
    pub name: String,
    pub symbol: String,
    pub params: Vec<String>,
    pub return_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PluginClassEntry {
    pub name: String,
    pub constructor: String,
    pub destructor: String,
    pub methods: Vec<PluginMethodEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PluginEntry {
    pub name: String,
    pub library: String,
    pub version: Option<String>,
    pub functions: Vec<String>,
    pub classes: Vec<PluginClassEntry>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PluginManifest {
    pub plugins: Vec<PluginEntry>,
    pub symbols: HashSet<String>,
    pub symbol_to_library: HashMap<String, String>,
}

#[derive(Debug, Clone, Default)]
pub struct PluginManifestCache {
    pub loaded: bool,
    pub manifest: PluginManifest,
    pub error: Option<String>,
}

pub static PLUGIN_MANIFEST_CACHE: LazyLock<Mutex<PluginManifestCache>> =
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
    classes: &mut Vec<PluginClassEntry>,
) -> Result<(), String> {
    if name.trim().is_empty() && library.trim().is_empty() && functions.is_empty() && classes.is_empty() {
        return Ok(());
    }

    if name.trim().is_empty() {
        return Err("plugin entry missing non-empty 'name'".to_string());
    }
    if library.trim().is_empty() {
        return Err(format!("plugin '{}' missing non-empty 'library'", name.trim()));
    }
    if functions.is_empty() && classes.is_empty() {
        return Err(format!("plugin '{}' must declare at least one function or class", name.trim()));
    }

    plugins.push(PluginEntry {
        name: name.trim().to_string(),
        library: library.trim().to_string(),
        version: version.take(),
        functions: std::mem::take(functions),
        classes: std::mem::take(classes),
    });
    name.clear();
    library.clear();
    Ok(())
}

pub fn parse_plugin_manifest(path: &Path) -> Result<PluginManifest, String> {
    if !path.exists() {
        return Ok(PluginManifest::default());
    }

    let content =
        fs::read_to_string(path).map_err(|e| format!("failed to read plugin manifest '{}': {}", path.display(), e))?;

    let mut plugins = Vec::new();
    let mut current_name = String::new();
    let mut current_library = String::new();
    let mut current_version = None;
    let mut current_functions = Vec::new();
    let mut current_classes: Vec<PluginClassEntry> = Vec::new();
    let mut in_plugins_section = false;

    // Class parsing state
    let mut in_classes_block = false;
    let mut class_name = String::new();
    let mut class_constructor = String::new();
    let mut class_destructor = String::new();
    let mut class_methods: Vec<PluginMethodEntry> = Vec::new();
    let mut in_methods_block = false;
    let mut method_name = String::new();
    let mut method_symbol = String::new();
    let mut method_params: Vec<String> = Vec::new();
    let mut method_return_type = String::new();

    let lines: Vec<&str> = content.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let raw_line = lines[i];
        let line = raw_line.trim();
        i += 1;

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

        // Determine indentation level (number of leading spaces)
        let indent = raw_line.len() - raw_line.trim_start().len();

        if line == "-" {
            // Flush any in-progress method
            if !method_name.is_empty() {
                class_methods.push(PluginMethodEntry {
                    name: std::mem::take(&mut method_name),
                    symbol: std::mem::take(&mut method_symbol),
                    params: std::mem::take(&mut method_params),
                    return_type: std::mem::take(&mut method_return_type),
                });
            }
            // Flush any in-progress class
            if !class_name.is_empty() {
                current_classes.push(PluginClassEntry {
                    name: std::mem::take(&mut class_name),
                    constructor: std::mem::take(&mut class_constructor),
                    destructor: std::mem::take(&mut class_destructor),
                    methods: std::mem::take(&mut class_methods),
                });
            }
            in_classes_block = false;
            in_methods_block = false;

            finalize_plugin_entry(
                &mut plugins,
                &mut current_name,
                &mut current_library,
                &mut current_version,
                &mut current_functions,
                &mut current_classes,
            )?;
            continue;
        }

        // Inside a methods block — parsing individual method properties
        if in_methods_block && indent >= 20 {
            if let Some(value) = line.strip_prefix("symbol:") {
                method_symbol = strip_quotes(value).trim().to_string();
                continue;
            }
            if line.starts_with("params:") {
                method_params = parse_functions_line(line);
                continue;
            }
            if let Some(value) = line.strip_prefix("return:") {
                method_return_type = strip_quotes(value).trim().to_string();
                continue;
            }
        }

        // Inside methods block — a new method name (indented under methods:)
        if in_methods_block && indent >= 16 && line.ends_with(':') && !line.starts_with("symbol:") && !line.starts_with("params:") && !line.starts_with("return:") {
            // Flush previous method if any
            if !method_name.is_empty() {
                class_methods.push(PluginMethodEntry {
                    name: std::mem::take(&mut method_name),
                    symbol: std::mem::take(&mut method_symbol),
                    params: std::mem::take(&mut method_params),
                    return_type: std::mem::take(&mut method_return_type),
                });
            }
            method_name = line.trim_end_matches(':').trim().to_string();
            method_symbol.clear();
            method_params.clear();
            method_return_type.clear();
            continue;
        }

        // Inside a classes block — parsing class-level properties
        if in_classes_block && indent >= 12 {
            if let Some(value) = line.strip_prefix("constructor:") {
                class_constructor = strip_quotes(value).trim().to_string();
                continue;
            }
            if let Some(value) = line.strip_prefix("destructor:") {
                class_destructor = strip_quotes(value).trim().to_string();
                continue;
            }
            if line == "methods:" {
                in_methods_block = true;
                continue;
            }
        }

        // Inside classes block — a new class name
        if in_classes_block && indent >= 8 && line.ends_with(':') && !line.starts_with("constructor:") && !line.starts_with("destructor:") && !line.starts_with("methods:") {
            // Flush previous method if any
            if !method_name.is_empty() {
                class_methods.push(PluginMethodEntry {
                    name: std::mem::take(&mut method_name),
                    symbol: std::mem::take(&mut method_symbol),
                    params: std::mem::take(&mut method_params),
                    return_type: std::mem::take(&mut method_return_type),
                });
            }
            // Flush previous class if any
            if !class_name.is_empty() {
                current_classes.push(PluginClassEntry {
                    name: std::mem::take(&mut class_name),
                    constructor: std::mem::take(&mut class_constructor),
                    destructor: std::mem::take(&mut class_destructor),
                    methods: std::mem::take(&mut class_methods),
                });
            }
            class_name = line.trim_end_matches(':').trim().to_string();
            class_constructor.clear();
            class_destructor.clear();
            class_methods.clear();
            in_methods_block = false;
            continue;
        }

        if line == "classes:" {
            in_classes_block = true;
            in_methods_block = false;
            continue;
        }

        // Existing top-level entry fields
        if let Some(value) = line.strip_prefix("name:") {
            in_classes_block = false;
            in_methods_block = false;
            current_name = strip_quotes(value).trim().to_string();
            continue;
        }
        if let Some(value) = line.strip_prefix("library:") {
            in_classes_block = false;
            in_methods_block = false;
            current_library = strip_quotes(value).trim().to_string();
            continue;
        }
        if let Some(value) = line.strip_prefix("version:") {
            in_classes_block = false;
            in_methods_block = false;
            let parsed = strip_quotes(value).trim().to_string();
            current_version = if parsed.is_empty() { None } else { Some(parsed) };
            continue;
        }
        if line.starts_with("functions:") {
            in_classes_block = false;
            in_methods_block = false;
            current_functions = parse_functions_line(line);
        }
    }

    // Flush any in-progress method
    if !method_name.is_empty() {
        class_methods.push(PluginMethodEntry {
            name: std::mem::take(&mut method_name),
            symbol: std::mem::take(&mut method_symbol),
            params: std::mem::take(&mut method_params),
            return_type: std::mem::take(&mut method_return_type),
        });
    }
    // Flush any in-progress class
    if !class_name.is_empty() {
        current_classes.push(PluginClassEntry {
            name: std::mem::take(&mut class_name),
            constructor: std::mem::take(&mut class_constructor),
            destructor: std::mem::take(&mut class_destructor),
            methods: std::mem::take(&mut class_methods),
        });
    }

    finalize_plugin_entry(
        &mut plugins,
        &mut current_name,
        &mut current_library,
        &mut current_version,
        &mut current_functions,
        &mut current_classes,
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

        // Register class constructor, destructor, and method symbols
        for class in &entry.classes {
            if !class.constructor.is_empty() {
                if !symbols.insert(class.constructor.clone()) {
                    return Err(format!(
                        "plugin manifest '{}' declares duplicate extern symbol '{}'",
                        path.display(),
                        class.constructor
                    ));
                }
                symbol_to_library.insert(class.constructor.clone(), entry.library.clone());
            }
            if !class.destructor.is_empty() {
                if !symbols.insert(class.destructor.clone()) {
                    return Err(format!(
                        "plugin manifest '{}' declares duplicate extern symbol '{}'",
                        path.display(),
                        class.destructor
                    ));
                }
                symbol_to_library.insert(class.destructor.clone(), entry.library.clone());
            }
            for method in &class.methods {
                if !method.symbol.is_empty() {
                    if !symbols.insert(method.symbol.clone()) {
                        return Err(format!(
                            "plugin manifest '{}' declares duplicate extern symbol '{}'",
                            path.display(),
                            method.symbol
                        ));
                    }
                    symbol_to_library.insert(method.symbol.clone(), entry.library.clone());
                }
            }
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

    #[test]
    fn parses_manifest_with_classes() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("manifest.sdn");
        fs::write(
            &path,
            r#"
plugins:
    -
        name: math_lib
        library: /tmp/libmath.so
        version: "1.0.0"
        functions: [rt_math_init]
        classes:
            Calculator:
                constructor: spl_Calculator_create
                destructor: spl_Calculator_destroy
                methods:
                    add:
                        symbol: spl_Calculator_add
                        params: [handle, i64]
                        return: i64
                    get_result:
                        symbol: spl_Calculator_get_result
                        params: [handle]
                        return: i64
"#,
        )
        .unwrap();

        let manifest = parse_plugin_manifest(&path).unwrap();
        assert_eq!(manifest.plugins.len(), 1);

        let entry = &manifest.plugins[0];
        assert_eq!(entry.name, "math_lib");
        assert_eq!(entry.functions.len(), 1);
        assert_eq!(entry.classes.len(), 1);

        let class = &entry.classes[0];
        assert_eq!(class.name, "Calculator");
        assert_eq!(class.constructor, "spl_Calculator_create");
        assert_eq!(class.destructor, "spl_Calculator_destroy");
        assert_eq!(class.methods.len(), 2);
        assert_eq!(class.methods[0].name, "add");
        assert_eq!(class.methods[0].symbol, "spl_Calculator_add");
        assert_eq!(class.methods[0].params, vec!["handle", "i64"]);
        assert_eq!(class.methods[0].return_type, "i64");
        assert_eq!(class.methods[1].name, "get_result");
        assert_eq!(class.methods[1].symbol, "spl_Calculator_get_result");

        // Verify all class symbols are registered
        assert!(manifest.symbols.contains("spl_Calculator_create"));
        assert!(manifest.symbols.contains("spl_Calculator_destroy"));
        assert!(manifest.symbols.contains("spl_Calculator_add"));
        assert!(manifest.symbols.contains("spl_Calculator_get_result"));
        assert_eq!(
            manifest.symbol_to_library.get("spl_Calculator_add"),
            Some(&"/tmp/libmath.so".to_string())
        );
    }

    #[test]
    fn parses_manifest_with_classes_only() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("manifest.sdn");
        fs::write(
            &path,
            r#"
plugins:
    -
        name: calc_lib
        library: /tmp/libcalc.so
        classes:
            Adder:
                constructor: spl_Adder_new
                destructor: spl_Adder_free
                methods:
                    add:
                        symbol: spl_Adder_add
                        params: [handle, i64]
                        return: i64
"#,
        )
        .unwrap();

        let manifest = parse_plugin_manifest(&path).unwrap();
        assert_eq!(manifest.plugins.len(), 1);
        assert_eq!(manifest.plugins[0].functions.len(), 0);
        assert_eq!(manifest.plugins[0].classes.len(), 1);
        assert_eq!(manifest.plugins[0].classes[0].name, "Adder");
    }

    #[test]
    fn parses_manifest_with_multiple_classes() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("manifest.sdn");
        fs::write(
            &path,
            r#"
plugins:
    -
        name: multi_lib
        library: /tmp/libmulti.so
        classes:
            Foo:
                constructor: spl_Foo_new
                destructor: spl_Foo_free
                methods:
                    bar:
                        symbol: spl_Foo_bar
                        params: [handle]
                        return: i64
            Baz:
                constructor: spl_Baz_new
                destructor: spl_Baz_free
                methods:
                    qux:
                        symbol: spl_Baz_qux
                        params: [handle, i64]
                        return: i64
"#,
        )
        .unwrap();

        let manifest = parse_plugin_manifest(&path).unwrap();
        assert_eq!(manifest.plugins[0].classes.len(), 2);
        assert_eq!(manifest.plugins[0].classes[0].name, "Foo");
        assert_eq!(manifest.plugins[0].classes[1].name, "Baz");
    }
}
