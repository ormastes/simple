//! `UnitRegistry` — Rust-seed mirror of the pure-Simple
//! `src/compiler/30.types/units/unit_registry.spl`.
//!
//! Built once per process by scanning `src/unit/simple-lang/**/*.spl` for unit
//! `class` files. Each unit class exposes a fixed set of `static fn` accessors
//! that we extract with a small line-based parser (no full AST):
//!
//! ```text
//! static fn symbol() -> text: "km"
//! static fn kind() -> text: "Length"
//! static fn scale_to_base() -> f64: 1000.0
//! static fn base_unit() -> text: "m"
//! static fn numerator() -> [text]: ["km"]      # composites only
//! static fn denominator() -> [text]: ["h"]     # composites only
//! ```
//!
//! Once loaded, the registry seeds the legacy thread-local unit state
//! (`UNIT_SUFFIX_TO_FAMILY`, `UNIT_FAMILY_CONVERSIONS`, `BASE_UNIT_DIMENSIONS`,
//! `COMPOUND_UNIT_DIMENSIONS`) so the existing dimension-analysis machinery in
//! `interpreter_unit.rs` keeps working without further surgery.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// One catalogued unit. Matches the pure-Simple `UnitEntry` shape.
#[derive(Debug, Clone)]
pub struct UnitEntry {
    pub symbol: String,
    pub kind: String,
    pub scale_to_base: f64,
    pub base_unit: String,
    /// Dimension signature: base-unit-symbol -> exponent. For atomic units
    /// (`km`) this is `{base_unit: 1}`. For composites parsed from
    /// `numerator() / denominator()` this is the folded signature
    /// (`kmph` -> `{"m": 1, "s": -1}`).
    pub dimensions: HashMap<String, i32>,
}

/// Process-wide unit registry built from `src/unit/simple-lang/`.
#[derive(Debug, Default, Clone)]
pub struct UnitRegistry {
    pub entries: HashMap<String, UnitEntry>,
}

impl UnitRegistry {
    pub fn new() -> Self {
        UnitRegistry { entries: HashMap::new() }
    }

    pub fn lookup(&self, symbol: &str) -> Option<&UnitEntry> {
        self.entries.get(symbol)
    }

    /// Find an entry whose dimension signature matches `dims` exactly.
    /// Used after unit arithmetic to discover composite names like `kmph`.
    pub fn lookup_by_dimensions(&self, dims: &HashMap<String, i32>) -> Option<&UnitEntry> {
        // Prefer composites (more than one base) so we surface `kmph` not `m`
        // when a base unit happens to share a signature with a composite.
        let mut best: Option<&UnitEntry> = None;
        for entry in self.entries.values() {
            if dimensions_eq(&entry.dimensions, dims) {
                match best {
                    None => best = Some(entry),
                    Some(prev) => {
                        // Tie-break: prefer the entry with more dimension
                        // components (more "composite-like"), then shorter
                        // symbol for stability.
                        if entry.dimensions.len() > prev.dimensions.len()
                            || (entry.dimensions.len() == prev.dimensions.len()
                                && entry.symbol.len() < prev.symbol.len())
                        {
                            best = Some(entry);
                        }
                    }
                }
            }
        }
        best
    }
}

fn dimensions_eq(a: &HashMap<String, i32>, b: &HashMap<String, i32>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    for (k, v) in a {
        match b.get(k) {
            Some(other) if other == v => {}
            _ => return false,
        }
    }
    true
}

/// Convert `value` from the unit `from` to the unit `to`. Both must be
/// registered. Errors when symbols are unknown or dimensions disagree.
pub fn convert(value: f64, from: &str, to: &str) -> Result<f64, String> {
    let reg = ensure_loaded();
    let from_entry = reg
        .lookup(from)
        .ok_or_else(|| format!("unit '{}' not registered", from))?;
    let to_entry = reg
        .lookup(to)
        .ok_or_else(|| format!("unit '{}' not registered", to))?;
    if !dimensions_eq(&from_entry.dimensions, &to_entry.dimensions) {
        return Err(format!(
            "cannot convert '{}' to '{}': dimension mismatch",
            from, to
        ));
    }
    if to_entry.scale_to_base == 0.0 {
        return Err(format!("unit '{}' has zero scale_to_base", to));
    }
    Ok(value * (from_entry.scale_to_base / to_entry.scale_to_base))
}

/// True iff both symbols are registered and share the same dimension
/// signature.
pub fn dimensions_match(a: &str, b: &str) -> bool {
    let reg = ensure_loaded();
    match (reg.lookup(a), reg.lookup(b)) {
        (Some(ea), Some(eb)) => dimensions_eq(&ea.dimensions, &eb.dimensions),
        _ => false,
    }
}

/// Look up an entry by symbol against the lazily-loaded global registry.
pub fn lookup(symbol: &str) -> Option<UnitEntry> {
    ensure_loaded().lookup(symbol).cloned()
}

/// Look up an entry whose dimension signature matches `dims`.
pub fn lookup_by_dimensions(dims: &HashMap<String, i32>) -> Option<UnitEntry> {
    ensure_loaded().lookup_by_dimensions(dims).cloned()
}

// ---------------------------------------------------------------------------
// Lazy global registry
// ---------------------------------------------------------------------------

static GLOBAL: OnceLock<UnitRegistry> = OnceLock::new();

thread_local! {
    /// Tracks whether the calling thread has already mirrored the registry
    /// into the legacy thread-local unit state. Each new thread re-seeds.
    static THREAD_SEEDED: RefCell<bool> = const { RefCell::new(false) };
}

/// Get the process-wide registry, building it on first use.
pub fn ensure_loaded() -> &'static UnitRegistry {
    let dbg = std::env::var("SIMPLE_UNIT_REGISTRY_DEBUG").is_ok();
    let reg = GLOBAL.get_or_init(|| {
        let root = find_unit_tree_root();
        if dbg {
            eprintln!("[unit-registry] init: root = {:?}", root);
        }
        match root {
            Some(p) => build_from_unit_tree(&p).unwrap_or_else(|err| {
                eprintln!("[unit-registry] scan failed at {}: {}", p.display(), err);
                UnitRegistry::new()
            }),
            None => UnitRegistry::new(),
        }
    });
    if dbg {
        eprintln!("[unit-registry] ensure_loaded called; entries={}", reg.entries.len());
    }
    populate_thread_local_state(reg);
    reg
}

/// Mirror the registry contents into the legacy thread-local unit state used
/// by `interpreter_unit.rs`. Idempotent per thread — a thread that already
/// holds populated `UNIT_SUFFIX_TO_FAMILY` entries from a `use unit.*` module
/// load will not be re-seeded (we treat user state as authoritative).
pub fn populate_thread_local_state(reg: &UnitRegistry) {
    let needs_seed = THREAD_SEEDED.with(|cell| {
        let mut cell = cell.borrow_mut();
        if *cell {
            false
        } else {
            *cell = true;
            true
        }
    });
    if !needs_seed {
        return;
    }

    use crate::interpreter::{
        BASE_UNIT_DIMENSIONS, COMPOUND_UNIT_DIMENSIONS, SI_BASE_UNITS, UNIT_FAMILY_CONVERSIONS, UNIT_SUFFIX_TO_FAMILY,
    };
    use crate::interpreter_unit::Dimension;

    // The existing dimension-analysis machinery in `interpreter_unit.rs` keys
    // dimensions by family name (e.g. `Dimension::base("length")` → `{length:
    // 1}`), and the lowercase form is what user `unit length:` declarations
    // register. We mirror that convention here: kind strings from `static fn
    // kind()` are normalised to lowercase before being used as family names
    // and dimension keys. This also resolves the AC-4 PascalCase/lowercase
    // mismatch noted in the design doc.

    // family-name (lowercase) -> { suffix -> scale_to_base }
    let mut by_family: HashMap<String, HashMap<String, f64>> = HashMap::new();
    // suffix -> family-name (lowercase)
    let mut by_suffix: HashMap<String, String> = HashMap::new();
    // family-name (lowercase) -> Dimension keyed by family-name
    let mut family_dims: HashMap<String, Dimension> = HashMap::new();
    // composite-suffix -> Dimension keyed by family-name
    let mut compound_dims: HashMap<String, Dimension> = HashMap::new();
    // base-suffix -> family-name (for SI prefix decomposition: "m" -> "length")
    let mut si_bases: HashMap<String, String> = HashMap::new();

    // First sweep: build base-unit-symbol -> family-name (lowercase) so the
    // composite pass can translate dims like `{m: 1, s: -1}` into
    // `{length: 1, time: -1}`.
    let mut base_symbol_to_family: HashMap<String, String> = HashMap::new();
    for entry in reg.entries.values() {
        if entry.dimensions.len() == 1 && (entry.scale_to_base - 1.0).abs() < f64::EPSILON {
            // This is the canonical base unit for its family.
            let family = entry.kind.to_ascii_lowercase();
            base_symbol_to_family
                .entry(entry.symbol.clone())
                .or_insert(family);
        }
    }

    for entry in reg.entries.values() {
        if entry.kind.is_empty() {
            continue;
        }
        let family = entry.kind.to_ascii_lowercase();
        by_suffix.entry(entry.symbol.clone()).or_insert_with(|| family.clone());
        by_family
            .entry(family.clone())
            .or_default()
            .insert(entry.symbol.clone(), entry.scale_to_base);

        // Translate base-symbol-keyed dims to family-name-keyed dims.
        let mut translated: HashMap<String, i32> = HashMap::new();
        for (base_sym, exp) in &entry.dimensions {
            let key = base_symbol_to_family
                .get(base_sym)
                .cloned()
                .unwrap_or_else(|| base_sym.clone());
            *translated.entry(key).or_insert(0) += *exp;
        }
        translated.retain(|_, v| *v != 0);
        let dim = Dimension { exponents: translated };

        if dim.exponents.len() > 1 {
            // Composite — record its dimension signature so dimension-lookup
            // can find it by signature (e.g. {length:1, time:-1} → "kmph").
            compound_dims.insert(entry.symbol.clone(), dim);
        } else if dim.exponents.len() == 1 {
            // Atomic unit — record the canonical base dimension for the
            // family if not yet present.
            family_dims
                .entry(family.clone())
                .or_insert_with(|| Dimension::base(&family));
            if (entry.scale_to_base - 1.0).abs() < f64::EPSILON {
                si_bases.entry(entry.symbol.clone()).or_insert(family);
            }
        }
    }

    // Merge into the thread-locals. Existing entries (planted by user `use
    // unit.*` module evaluation) win — we only fill gaps.
    let dbg = std::env::var("SIMPLE_UNIT_REGISTRY_DEBUG").is_ok();
    if dbg {
        eprintln!(
            "[unit-registry] seed: {} suffixes, {} families, {} compound, {} si_bases",
            by_suffix.len(),
            by_family.len(),
            compound_dims.len(),
            si_bases.len(),
        );
        if let Some(v) = by_family.get("velocity") {
            eprintln!("[unit-registry] velocity family conversions: {:?}", v);
        }
        if let Some(v) = compound_dims.get("kmph") {
            eprintln!("[unit-registry] kmph compound dim: {:?}", v.exponents);
        }
    }
    UNIT_SUFFIX_TO_FAMILY.with(|cell| {
        let mut map = cell.borrow_mut();
        for (k, v) in by_suffix {
            map.entry(k).or_insert(v);
        }
    });
    UNIT_FAMILY_CONVERSIONS.with(|cell| {
        let mut map = cell.borrow_mut();
        for (family, conversions) in by_family {
            let entry = map.entry(family).or_default();
            for (k, v) in conversions {
                entry.entry(k).or_insert(v);
            }
        }
    });
    BASE_UNIT_DIMENSIONS.with(|cell| {
        let mut map = cell.borrow_mut();
        for (k, v) in family_dims {
            map.entry(k).or_insert(v);
        }
    });
    COMPOUND_UNIT_DIMENSIONS.with(|cell| {
        let mut map = cell.borrow_mut();
        for (k, v) in compound_dims {
            map.entry(k).or_insert(v);
        }
    });
    SI_BASE_UNITS.with(|cell| {
        let mut map = cell.borrow_mut();
        for (k, v) in si_bases {
            map.entry(k).or_insert(v);
        }
    });
}

// ---------------------------------------------------------------------------
// Filesystem scan
// ---------------------------------------------------------------------------

/// Locate `src/unit/simple-lang/` by walking up from CARGO_MANIFEST_DIR. The
/// crate at `src/compiler_rust/compiler/` lives two ancestors below the repo
/// root, so a fixed offset works in dev. Falls back to env override or CWD.
fn find_unit_tree_root() -> Option<PathBuf> {
    if let Ok(custom) = std::env::var("SIMPLE_UNIT_TREE_ROOT") {
        let p = PathBuf::from(custom);
        if p.is_dir() {
            return Some(p);
        }
    }
    let candidates: Vec<PathBuf> = {
        let mut v = Vec::new();
        if let Some(manifest) = option_env!("CARGO_MANIFEST_DIR") {
            // src/compiler_rust/compiler -> walk up to repo root.
            let mut p = PathBuf::from(manifest);
            for _ in 0..6 {
                v.push(p.join("src/unit/simple-lang"));
                if !p.pop() {
                    break;
                }
            }
        }
        if let Ok(cwd) = std::env::current_dir() {
            let mut p = cwd;
            for _ in 0..6 {
                v.push(p.join("src/unit/simple-lang"));
                if !p.pop() {
                    break;
                }
            }
        }
        v
    };
    candidates.into_iter().find(|p| p.is_dir())
}

/// Walk `root_path` for `*.spl` unit-class files and build a registry.
pub fn build_from_unit_tree(root_path: &Path) -> Result<UnitRegistry, String> {
    let mut reg = UnitRegistry::new();
    let mut atomic_files: Vec<PathBuf> = Vec::new();
    let mut composite_files: Vec<PathBuf> = Vec::new();
    walk_spl_files(root_path, &mut |p| {
        let s = p.to_string_lossy();
        if s.contains("/composite/") {
            composite_files.push(p.to_path_buf());
        } else {
            atomic_files.push(p.to_path_buf());
        }
    })?;

    // First pass: atomic units. Their dimensions are `{base_unit: 1}`.
    for f in &atomic_files {
        if let Some(mut entry) = parse_unit_file(f) {
            if entry.dimensions.is_empty() && !entry.base_unit.is_empty() {
                let mut dims = HashMap::new();
                dims.insert(entry.base_unit.clone(), 1);
                entry.dimensions = dims;
            }
            // Last writer wins on duplicate symbols (e.g. velocity/mps_v
            // shims). The composite pass will overwrite for derived units.
            reg.entries.insert(entry.symbol.clone(), entry);
        }
    }

    // Second pass: composites. Dimensions are folded from numerator() and
    // denominator() symbol lists by looking up atomic entries.
    for f in &composite_files {
        if let Some(mut entry) = parse_unit_file(f) {
            let dims = fold_composite_dimensions(&entry, &reg);
            entry.dimensions = dims;
            reg.entries.insert(entry.symbol.clone(), entry);
        }
    }

    Ok(reg)
}

fn walk_spl_files(root: &Path, sink: &mut dyn FnMut(&Path)) -> Result<(), String> {
    let entries = std::fs::read_dir(root).map_err(|e| format!("read_dir {}: {}", root.display(), e))?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            // Skip __pycache__ etc. if present.
            walk_spl_files(&path, sink)?;
        } else if path.extension().and_then(|s| s.to_str()) == Some("spl") {
            // Skip __init__.spl re-exporters; they don't define unit classes.
            if path.file_name().and_then(|s| s.to_str()) == Some("__init__.spl") {
                continue;
            }
            sink(&path);
        }
    }
    Ok(())
}

fn fold_composite_dimensions(entry: &UnitEntry, reg: &UnitRegistry) -> HashMap<String, i32> {
    // If the parser already populated dimensions, trust them.
    if !entry.dimensions.is_empty() {
        return entry.dimensions.clone();
    }
    let mut dims: HashMap<String, i32> = HashMap::new();
    // numerator()/denominator() were stashed in dimensions via sentinel keys
    // by `parse_unit_file`. Walk the placeholder lists.
    // We use distinct sentinel prefixes "__num__:N" / "__den__:N" only inside
    // the parser; here we re-look them up via attached side data — but to
    // keep the scan single-pass we instead re-parse the file path's pieces.
    // Simpler: use any cached numerator/denominator on the entry's
    // `composite_parts` when we parse. We piggy-back via a per-symbol map
    // populated during parse_unit_file. See PARSED_PARTS below.
    let parts = PARSED_PARTS.with(|cell| cell.borrow().get(&entry.symbol).cloned());
    if let Some((num, den)) = parts {
        for sym in num {
            if let Some(child) = reg.lookup(&sym) {
                for (b, e) in &child.dimensions {
                    *dims.entry(b.clone()).or_insert(0) += e;
                }
            } else if !sym.is_empty() {
                *dims.entry(sym, ).or_insert(0) += 1;
            }
        }
        for sym in den {
            if let Some(child) = reg.lookup(&sym) {
                for (b, e) in &child.dimensions {
                    *dims.entry(b.clone()).or_insert(0) -= e;
                }
            } else if !sym.is_empty() {
                *dims.entry(sym, ).or_insert(0) -= 1;
            }
        }
    } else if !entry.base_unit.is_empty() {
        // Composite without numerator/denominator metadata — fall back to
        // splitting `base_unit` on "/" and "*". Limited but useful.
        dims = parse_inline_dimension(&entry.base_unit);
    }
    dims.retain(|_, v| *v != 0);
    dims
}

fn parse_inline_dimension(text: &str) -> HashMap<String, i32> {
    // Very small parser for "m/s" or "kg*m/s^2"-style strings. Powers via "^".
    let mut dims: HashMap<String, i32> = HashMap::new();
    let mut sign: i32 = 1;
    let mut current = String::new();
    let mut chars = text.chars().peekable();
    let flush = |sym: &mut String, sign: i32, dims: &mut HashMap<String, i32>| {
        let s = sym.trim();
        if s.is_empty() {
            sym.clear();
            return;
        }
        let (name, exp) = match s.split_once('^') {
            Some((n, e)) => (n.trim().to_string(), e.trim().parse::<i32>().unwrap_or(1)),
            None => (s.to_string(), 1),
        };
        *dims.entry(name).or_insert(0) += sign * exp;
        sym.clear();
    };
    while let Some(c) = chars.next() {
        match c {
            '*' | ' ' | '·' => {
                flush(&mut current, sign, &mut dims);
            }
            '/' => {
                flush(&mut current, sign, &mut dims);
                sign = -1;
            }
            other => current.push(other),
        }
    }
    flush(&mut current, sign, &mut dims);
    dims.retain(|_, v| *v != 0);
    dims
}

thread_local! {
    /// During registry build we stash composite numerator/denominator lists
    /// keyed by symbol so the second pass can fold dimensions without
    /// re-parsing. Cleared after build.
    static PARSED_PARTS: RefCell<HashMap<String, (Vec<String>, Vec<String>)>> = RefCell::new(HashMap::new());
}

fn parse_unit_file(path: &Path) -> Option<UnitEntry> {
    let src = std::fs::read_to_string(path).ok()?;
    let mut symbol = String::new();
    let mut kind = String::new();
    let mut scale: f64 = 1.0;
    let mut base_unit = String::new();
    let mut numerator: Vec<String> = Vec::new();
    let mut denominator: Vec<String> = Vec::new();

    for raw in src.lines() {
        let line = raw.trim();
        if !line.starts_with("static fn ") {
            continue;
        }
        // `static fn symbol() -> text: "km"`
        if let Some(s) = extract_string_static(line, "symbol") {
            symbol = s;
        } else if let Some(s) = extract_string_static(line, "kind") {
            kind = s;
        } else if let Some(s) = extract_string_static(line, "base_unit") {
            base_unit = s;
        } else if let Some(s) = extract_after_colon(line, "scale_to_base") {
            // accept `1000.0`, `1e-3`, `0.277777777777778`
            if let Ok(n) = s.trim().parse::<f64>() {
                scale = n;
            }
        } else if let Some(list) = extract_text_list(line, "numerator") {
            numerator = list;
        } else if let Some(list) = extract_text_list(line, "denominator") {
            denominator = list;
        }
    }

    if symbol.is_empty() {
        return None;
    }

    if !numerator.is_empty() || !denominator.is_empty() {
        PARSED_PARTS.with(|cell| {
            cell.borrow_mut()
                .insert(symbol.clone(), (numerator.clone(), denominator.clone()));
        });
    }

    Some(UnitEntry {
        symbol,
        kind,
        scale_to_base: scale,
        base_unit,
        dimensions: HashMap::new(),
    })
}

fn extract_string_static(line: &str, name: &str) -> Option<String> {
    // matches: static fn <name>() -> text: "VALUE"
    let needle = format!("static fn {}()", name);
    if !line.starts_with(&needle) {
        return None;
    }
    // find first '"' after ':'
    let after_colon = line.split_once(':')?.1.trim();
    let bytes = after_colon.as_bytes();
    if bytes.first() != Some(&b'"') {
        return None;
    }
    let mut end = 1;
    while end < bytes.len() && bytes[end] != b'"' {
        end += 1;
    }
    if end >= bytes.len() {
        return None;
    }
    Some(after_colon[1..end].to_string())
}

fn extract_after_colon<'a>(line: &'a str, name: &str) -> Option<&'a str> {
    let needle = format!("static fn {}()", name);
    if !line.starts_with(&needle) {
        return None;
    }
    line.split_once(':').map(|(_, rest)| rest)
}

fn extract_text_list(line: &str, name: &str) -> Option<Vec<String>> {
    let needle = format!("static fn {}()", name);
    if !line.starts_with(&needle) {
        return None;
    }
    let after_colon = line.split_once(':')?.1.trim();
    if !after_colon.starts_with('[') || !after_colon.ends_with(']') {
        return None;
    }
    let inner = &after_colon[1..after_colon.len() - 1];
    let mut out = Vec::new();
    for raw in inner.split(',') {
        let s = raw.trim().trim_matches('"').to_string();
        if !s.is_empty() {
            out.push(s);
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_inline_dimension_m_per_s() {
        let dims = parse_inline_dimension("m/s");
        assert_eq!(dims.get("m"), Some(&1));
        assert_eq!(dims.get("s"), Some(&-1));
    }

    #[test]
    fn parse_inline_dimension_with_power() {
        let dims = parse_inline_dimension("kg*m/s^2");
        assert_eq!(dims.get("kg"), Some(&1));
        assert_eq!(dims.get("m"), Some(&1));
        assert_eq!(dims.get("s"), Some(&-2));
    }

    #[test]
    fn extract_string_static_simple() {
        let line = r#"static fn symbol() -> text: "km""#;
        assert_eq!(extract_string_static(line, "symbol").as_deref(), Some("km"));
    }

    #[test]
    fn extract_text_list_pair() {
        let line = r#"static fn numerator() -> [text]: ["km"]"#;
        assert_eq!(extract_text_list(line, "numerator"), Some(vec!["km".to_string()]));
    }

    #[test]
    fn dimensions_eq_basic() {
        let mut a: HashMap<String, i32> = HashMap::new();
        a.insert("m".into(), 1);
        a.insert("s".into(), -1);
        let mut b = a.clone();
        assert!(dimensions_eq(&a, &b));
        b.insert("kg".into(), 1);
        assert!(!dimensions_eq(&a, &b));
    }
}
