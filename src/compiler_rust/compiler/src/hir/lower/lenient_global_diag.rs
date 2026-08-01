//! Attribution for names that `lenient_types` lowers to `HirExprKind::Global`.
//!
//! # Why this exists
//!
//! Under `lenient_types`, an identifier that HIR lowering cannot resolve does
//! not error: it becomes `HirExprKind::Global(name)`, which becomes
//! `MirInst::GlobalLoad`, which becomes an *undeclared symbol* in the emitted
//! object. If nothing else in the program defines that symbol, the failure
//! surfaces at **link** time as a bare symbol name with no file, no line and no
//! enclosing function -- thousands of lines away from the identifier that
//! caused it.
//!
//! That has repeatedly converted ordinary typos and HIR scope bugs into
//! blockers that look unfixable. Two worked examples:
//!
//! * `interp_list` -- a compiler bug. `Expr::If` carries a `let_pattern` field
//!   that the HIR dispatcher matched with `..` and dropped, so `lower_if` never
//!   registered the bound name. Fixed in `a1c93dd7167`.
//! * `animation_time_ms` -- a plain undefined identifier in
//!   `_simple_web_layout_compose_retained`, referenced once and declared
//!   nowhere.
//!
//! Neither produced a single diagnostic before the linker ran.
//!
//! # Why this is a warning and not an error
//!
//! The fallback is **load-bearing**, so it cannot simply be made strict.
//! `native_project`'s `lower_file` lowers one file at a time and `self.globals`
//! is populated only from the current AST module's own items; nothing
//! repopulates it afterwards. A reference to a function, const or enum variant
//! that lives in a sibling file is therefore *necessarily* unresolvable at HIR
//! time and must survive as a `Global` so that codegen can resolve it against
//! `use_map` / `import_map` with `Linkage::Import`. Erroring here would break
//! all cross-module compilation.
//!
//! So this module does not change what is compiled. It only records *where each
//! unresolved name came from*, so that a link-time "undefined symbol X" can be
//! traced back to the file, function and line that produced it.
//!
//! # Cost and default
//!
//! Because legitimate cross-module references also take this path, the
//! population is dominated by names that are perfectly fine. Printing every one
//! by default would be noise, so the per-name listing is level-gated and
//! **default off**, enabled with:
//!
//! ```text
//! SIMPLE_DIAG_LENIENT_GLOBALS=1   # print each attributed name to stderr
//! ```
//!
//! Collection itself is always on and dedup'd; it is a few hundred entries at
//! most per file and is what makes the count reportable.

use std::collections::BTreeSet;

/// Which lenient fallback produced the `Global`.
///
/// Kept distinct because the right fix differs: an unresolved plain identifier
/// is usually a typo or a scope bug, whereas an unresolved `@rt_*` name is a
/// missing extern registration (which the native linker will happily satisfy
/// with a weak `return 0` stub).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LenientGlobalKind {
    /// A plain identifier that resolved to no local, no callable and no global.
    UnresolvedIdentifier,
    /// An `@name` SFFI reference with no matching extern declaration.
    UnresolvedSffiExtern,
    /// `Type.new(..)` lowered as a global instead of a constructor.
    ConstructorAsGlobal,
    /// A dotted path (`a.b.c`) lowered as a single dotted global name.
    UnresolvedPath,
}

impl LenientGlobalKind {
    pub fn as_str(self) -> &'static str {
        match self {
            LenientGlobalKind::UnresolvedIdentifier => "unresolved identifier",
            LenientGlobalKind::UnresolvedSffiExtern => "unresolved sffi extern",
            LenientGlobalKind::ConstructorAsGlobal => "constructor as global",
            LenientGlobalKind::UnresolvedPath => "unresolved path",
        }
    }
}

/// One attributed name. Ordering is (file, function, name, kind) so that the
/// dedup'd report reads grouped by source location.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LenientGlobal {
    /// Source file the reference appeared in, if the lowerer knew one.
    pub file: Option<String>,
    /// Enclosing function/method being lowered, if any.
    pub function: Option<String>,
    /// Declaration line of the enclosing function.
    ///
    /// `Expr::Identifier(String)` carries no span, so the *exact* line of the
    /// reference is not recoverable here without an AST change. The enclosing
    /// function's declaration line is the tightest attribution available and is
    /// enough to locate the name by grepping that function.
    pub function_line: Option<usize>,
    /// The name that was lowered as a global.
    pub name: String,
    /// Which fallback produced it.
    pub kind: LenientGlobalKind,
}

impl LenientGlobal {
    /// Human-readable one-line diagnostic.
    pub fn format(&self) -> String {
        let file = self.file.as_deref().unwrap_or("<unknown file>");
        let mut location = file.to_string();
        if let Some(line) = self.function_line {
            location.push(':');
            location.push_str(&line.to_string());
        }
        let context = match &self.function {
            Some(func) => format!(" in `{func}`"),
            None => String::new(),
        };
        format!(
            "warning: `{}` ({}) is being lowered as a global because it resolved to nothing at HIR time\n  --> {}{}\n   = note: if this name is not defined by another module it will fail at LINK time as an undefined symbol, with no source location [lenient_unresolved_global]",
            self.name,
            self.kind.as_str(),
            location,
            context
        )
    }
}

/// Dedup'd collector of names lowered as globals under `lenient_types`.
#[derive(Debug, Default, Clone)]
pub struct LenientGlobalCollector {
    entries: BTreeSet<LenientGlobal>,
}

impl LenientGlobalCollector {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one attributed name, deduplicating identical (file, function,
    /// name, kind) tuples. Returns `true` if this was newly recorded.
    pub fn record(&mut self, entry: LenientGlobal) -> bool {
        let is_new = self.entries.insert(entry.clone());
        if is_new && verbose_enabled() {
            eprintln!("{}", entry.format());
        }
        is_new
    }

    /// Number of distinct attributed names.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn entries(&self) -> impl Iterator<Item = &LenientGlobal> {
        self.entries.iter()
    }

    /// Look up every recorded attribution for a symbol name. This is the
    /// link-failure entry point: given "undefined symbol X" from the linker,
    /// this returns the source locations that emitted it.
    pub fn attributions_for(&self, name: &str) -> Vec<&LenientGlobal> {
        self.entries.iter().filter(|e| e.name == name).collect()
    }

    /// Merge another collector (per-file lowering runs produce one each).
    pub fn merge(&mut self, other: &LenientGlobalCollector) {
        for entry in &other.entries {
            self.entries.insert(entry.clone());
        }
    }
}

/// Level-gated: per-name printing is off unless `SIMPLE_DIAG_LENIENT_GLOBALS`
/// is set to something other than `0`/empty.
fn verbose_enabled() -> bool {
    match std::env::var("SIMPLE_DIAG_LENIENT_GLOBALS") {
        Ok(value) => !value.is_empty() && value != "0",
        Err(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(name: &str, func: Option<&str>) -> LenientGlobal {
        LenientGlobal {
            file: Some("src/app/web.spl".to_string()),
            function: func.map(|f| f.to_string()),
            function_line: Some(1570),
            name: name.to_string(),
            kind: LenientGlobalKind::UnresolvedIdentifier,
        }
    }

    #[test]
    fn dedups_identical_entries() {
        let mut collector = LenientGlobalCollector::new();
        assert!(collector.record(entry("animation_time_ms", Some("compose_retained"))));
        assert!(!collector.record(entry("animation_time_ms", Some("compose_retained"))));
        assert_eq!(collector.len(), 1);
    }

    #[test]
    fn distinct_functions_are_separate_entries() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(entry("interp_list", Some("a")));
        collector.record(entry("interp_list", Some("b")));
        assert_eq!(collector.len(), 2);
        assert_eq!(collector.attributions_for("interp_list").len(), 2);
    }

    #[test]
    fn format_names_file_line_function_and_link_consequence() {
        let text = entry("animation_time_ms", Some("_simple_web_layout_compose_retained")).format();
        assert!(text.contains("animation_time_ms"), "{text}");
        assert!(text.contains("src/app/web.spl:1570"), "{text}");
        assert!(text.contains("_simple_web_layout_compose_retained"), "{text}");
        assert!(text.contains("LINK"), "{text}");
    }

    #[test]
    fn attributions_for_unknown_name_is_empty() {
        let collector = LenientGlobalCollector::new();
        assert!(collector.attributions_for("nope").is_empty());
    }
}
