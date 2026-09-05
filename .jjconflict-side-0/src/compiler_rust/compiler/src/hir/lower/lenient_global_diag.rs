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
use std::sync::{Mutex, OnceLock};

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
    /// `file:line in `function`` -- the tightest source location available.
    pub fn location(&self) -> String {
        let file = self.file.as_deref().unwrap_or("<unknown file>");
        let mut location = file.to_string();
        if let Some(line) = self.function_line {
            location.push(':');
            location.push_str(&line.to_string());
        }
        if let Some(func) = &self.function {
            location.push_str(&format!(" in `{func}`"));
        }
        location
    }

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

    /// Attributions for a symbol name **as the linker reported it**.
    ///
    /// This differs from [`Self::attributions_for`], which matches the HIR name
    /// verbatim. A linker-reported name can differ from the HIR name by a
    /// platform or mangling artefact, so this tries the normalisation ladder in
    /// [`linker_symbol_candidates`] and returns the first non-empty match.
    pub fn attributions_for_linker_symbol(&self, symbol: &str) -> Vec<&LenientGlobal> {
        for candidate in linker_symbol_candidates(symbol) {
            let hits = self.attributions_for(&candidate);
            if !hits.is_empty() {
                return hits;
            }
        }
        Vec::new()
    }

    /// Turn raw linker output into a located diagnostic, or `None` when no
    /// undefined symbol in it was attributed during lowering.
    ///
    /// This is the whole point of the instrument: it converts
    /// `undefined symbol: interp_list` -- which names no file, no line and no
    /// function -- into the source locations that emitted it.
    pub fn explain_link_failure(&self, linker_output: &str) -> Option<String> {
        let symbols = undefined_symbols_in_linker_output(linker_output);
        if symbols.is_empty() {
            return None;
        }
        let mut sections: Vec<String> = Vec::new();
        for symbol in &symbols {
            let hits = self.attributions_for_linker_symbol(symbol);
            if hits.is_empty() {
                continue;
            }
            let mut lines = vec![format!(
                "note: `{symbol}` reached the linker undeclared because HIR lowering resolved it to nothing and the `lenient_types` fallback lowered it to a global. It is referenced at:"
            )];
            for hit in hits {
                lines.push(format!("  --> {} ({})", hit.location(), hit.kind.as_str()));
            }
            sections.push(lines.join("\n"));
        }
        if sections.is_empty() {
            return None;
        }
        sections.push(
            "note: attribution is function-granular because `Expr::Identifier` carries no span; grep the named function for the symbol [lenient_unresolved_global]"
                .to_string(),
        );
        Some(sections.join("\n"))
    }
}

/// Every undefined symbol named in linker output, in first-seen order.
///
/// Covers the three formats this project's link paths can produce:
/// GNU ``undefined reference to `sym'``, LLD/mold `undefined symbol: sym`, and
/// MSVC `unresolved external symbol sym referenced in function main`. A real
/// failure usually lists several, so this returns all of them rather than the
/// first.
pub fn undefined_symbols_in_linker_output(linker_output: &str) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    for line in linker_output.lines() {
        collect_marked_symbols(line, "undefined reference to `", Some('\''), &mut found);
        collect_marked_symbols(line, "undefined symbol: ", None, &mut found);
        collect_marked_symbols(line, "unresolved external symbol ", None, &mut found);
    }
    found
}

fn collect_marked_symbols(line: &str, marker: &str, closing: Option<char>, out: &mut Vec<String>) {
    let mut rest = line;
    while let Some(start) = rest.find(marker) {
        let tail = &rest[start + marker.len()..];
        let end = match closing {
            Some(close) => tail.find(close).unwrap_or(tail.len()),
            None => tail
                .find(|c: char| c.is_whitespace() || c == ',' || c == ';')
                .unwrap_or(tail.len()),
        };
        if end == 0 {
            return;
        }
        let symbol = tail[..end].trim();
        if !symbol.is_empty() && !out.iter().any(|existing| existing == symbol) {
            out.push(symbol.to_string());
        }
        rest = &tail[end..];
    }
}

fn push_candidate(out: &mut Vec<String>, candidate: String) {
    if !candidate.is_empty() && !out.iter().any(|existing| *existing == candidate) {
        out.push(candidate);
    }
}

/// Names to try when looking a linker-reported symbol up in the attribution
/// index, most-likely first.
///
/// A lenient unresolved global is by construction absent from `use_map` /
/// `import_map` and from `mir.local_globals`, so `native_project::mangle`
/// leaves it verbatim and the reported name normally *is* the HIR name. The
/// ladder exists for the residual cases: Mach-O/MSVC add a leading underscore,
/// `mangle::resolve_name` swaps `.` for `_dot_` in dotted paths, its
/// suffix fallback can prepend a `prefix__` module prefix, and SFFI references
/// are attributed with their `@` sigil, which is never emitted.
pub fn linker_symbol_candidates(symbol: &str) -> Vec<String> {
    let mut out = Vec::new();
    push_candidate(&mut out, symbol.to_string());
    if let Some(stripped) = symbol.strip_prefix('_') {
        push_candidate(&mut out, stripped.to_string());
    }
    for index in 0..out.len() {
        let base = out[index].clone();
        if base.contains("_dot_") {
            push_candidate(&mut out, base.replace("_dot_", "."));
        }
        if let Some(sep) = base.rfind("__") {
            push_candidate(&mut out, base[sep + 2..].to_string());
        }
    }
    for index in 0..out.len() {
        let base = out[index].clone();
        push_candidate(&mut out, format!("@{base}"));
    }
    out
}

/// Bound on the process-global registry, so a long-lived process (LSP, MCP
/// server) cannot grow it without limit. Entries are dedup'd tuples, so the
/// whole `src/compiler` + `src/lib` + `src/app` set fits well inside this.
const LINK_REGISTRY_CAP: usize = 100_000;

/// Process-global mirror of every attribution recorded by any `Lowerer`.
///
/// # Why a global and not a plumbed value
///
/// The link failure and the lowering that caused it happen in the same process
/// but are separated by an architecture that cannot carry a value between them:
/// `native_project::compiler::compile_file_to_object` calls
/// `Lowerer::lower_module`, which *consumes* the lowerer and returns only a
/// `HirModule`, and it is itself run on a spawned thread behind an `mpsc`
/// channel driven by a rayon pool, then the link runs from `&self` much later.
/// Threading a collector through that would change three signatures on the
/// production compile path purely for diagnostics. This registry is
/// append-only, dedup'd, capped, and read only on the link-failure path, so it
/// cannot affect what is compiled.
fn link_registry() -> &'static Mutex<LenientGlobalCollector> {
    static REGISTRY: OnceLock<Mutex<LenientGlobalCollector>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(LenientGlobalCollector::new()))
}

/// Mirror one attribution into the process-global registry.
///
/// Inserts directly rather than through `record`, because the owning `Lowerer`
/// has already done the level-gated print for this entry.
pub(super) fn record_for_link_diagnostics(entry: &LenientGlobal) {
    let Ok(mut registry) = link_registry().lock() else {
        return;
    };
    if registry.entries.len() >= LINK_REGISTRY_CAP {
        return;
    }
    registry.entries.insert(entry.clone());
}

/// Consult the process-global registry for a link failure.
///
/// This is the link-failure entry point used by the native link path. Returns
/// `None` when the output names no undefined symbol, or when none of the
/// undefined symbols were produced by the lenient fallback -- in which case the
/// linker's own message is already the best available diagnostic.
pub fn explain_link_failure(linker_output: &str) -> Option<String> {
    let registry = link_registry().lock().ok()?;
    registry.explain_link_failure(linker_output)
}

/// Number of attributions currently mirrored globally. Test/observability hook.
pub fn link_registry_len() -> usize {
    link_registry().lock().map(|r| r.entries.len()).unwrap_or(0)
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

    // ---- link-failure loop -------------------------------------------------

    #[test]
    fn extracts_gnu_lld_and_msvc_undefined_symbol_forms() {
        let output = "\
/usr/bin/ld: obj.o: in function `main':\n\
obj.o:(.text+0x10): undefined reference to `interp_list'\n\
ld.lld: error: undefined symbol: animation_time_ms\n\
foo.obj : error LNK2019: unresolved external symbol _widget_id referenced in function _main\n";
        let symbols = undefined_symbols_in_linker_output(output);
        assert_eq!(symbols, vec!["interp_list", "animation_time_ms", "_widget_id"]);
    }

    #[test]
    fn extracts_every_undefined_symbol_not_only_the_first() {
        // The pre-existing `NativeLinker::extract_undefined_symbol` returns
        // Option<String> and stops at the first hit, which would attribute only
        // one of a multi-symbol failure.
        let output = "undefined symbol: alpha\nundefined symbol: beta\nundefined symbol: gamma\n";
        assert_eq!(
            undefined_symbols_in_linker_output(output),
            vec!["alpha", "beta", "gamma"]
        );
    }

    #[test]
    fn repeated_symbol_is_reported_once() {
        let output = "undefined symbol: alpha\nundefined symbol: alpha\n";
        assert_eq!(undefined_symbols_in_linker_output(output), vec!["alpha"]);
    }

    #[test]
    fn clean_linker_output_names_no_symbols() {
        assert!(undefined_symbols_in_linker_output("ld: warning: something harmless\n").is_empty());
    }

    #[test]
    fn candidate_ladder_covers_underscore_dot_and_module_prefix() {
        assert_eq!(linker_symbol_candidates("plain")[0], "plain");
        assert!(linker_symbol_candidates("_widget_id").contains(&"widget_id".to_string()));
        assert!(linker_symbol_candidates("a_dot_b").contains(&"a.b".to_string()));
        assert!(linker_symbol_candidates("mod__thing").contains(&"thing".to_string()));
        assert!(linker_symbol_candidates("rt_x").contains(&"@rt_x".to_string()));
    }

    #[test]
    fn explain_link_failure_locates_an_attributed_symbol() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(entry("interp_list", Some("module_surface_from_module")));
        let report = collector
            .explain_link_failure("ld.lld: error: undefined symbol: interp_list\n")
            .expect("attributed symbol must produce a report");
        assert!(report.contains("interp_list"), "{report}");
        assert!(report.contains("src/app/web.spl:1570"), "{report}");
        assert!(report.contains("module_surface_from_module"), "{report}");
    }

    #[test]
    fn explain_link_failure_is_silent_for_unattributed_symbols() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(entry("interp_list", Some("f")));
        // A missing libc symbol is not our defect; the linker's own message is
        // already the best diagnostic and we must not add noise to it.
        assert!(collector
            .explain_link_failure("undefined reference to `pthread_create'\n")
            .is_none());
    }

    #[test]
    fn explain_link_failure_is_silent_when_nothing_is_undefined() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(entry("interp_list", Some("f")));
        assert!(collector.explain_link_failure("Linked: out (12 KB) via cc\n").is_none());
    }

    #[test]
    fn explain_link_failure_reports_all_attributed_symbols() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(entry("alpha", Some("fa")));
        collector.record(entry("beta", Some("fb")));
        let report = collector
            .explain_link_failure("undefined symbol: alpha\nundefined symbol: beta\n")
            .expect("both are attributed");
        assert!(report.contains("alpha") && report.contains("fa"), "{report}");
        assert!(report.contains("beta") && report.contains("fb"), "{report}");
    }

    #[test]
    fn linker_symbol_matches_through_the_macho_underscore_prefix() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(entry("widget_id", Some("compose")));
        assert_eq!(collector.attributions_for_linker_symbol("_widget_id").len(), 1);
        // The verbatim lookup must NOT match it -- that is the reason the
        // candidate ladder exists.
        assert!(collector.attributions_for("_widget_id").is_empty());
    }

    #[test]
    fn sffi_at_sigil_is_matched_from_the_unsigiled_linker_name() {
        let mut collector = LenientGlobalCollector::new();
        collector.record(LenientGlobal {
            file: Some("src/lib/x.spl".to_string()),
            function: Some("probe".to_string()),
            function_line: Some(3),
            name: "@rt_missing".to_string(),
            kind: LenientGlobalKind::UnresolvedSffiExtern,
        });
        assert_eq!(collector.attributions_for_linker_symbol("rt_missing").len(), 1);
    }
}
