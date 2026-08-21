//! Stub object generation for unresolved symbols during linking.

use std::path::{Path, PathBuf};

use simple_common::target::TargetOS;

use super::{effective_target, ModuleImports};
use super::tools::{
    find_c_compiler, find_runtime_library, is_compiler_rt_builtin_symbol, is_system_symbol, nm_command,
    target_c_compiler,
};

pub(crate) fn is_inline_asm_symbol(symbol: &str) -> bool {
    symbol.trim_start_matches('_').starts_with("simple_asm_")
}

fn is_linker_provided_symbol(sym: &str, defined: &std::collections::HashSet<String>) -> bool {
    matches!(
        sym,
        "_sbss"
            | "_ebss"
            | "__bss_start"
            | "__bss_end"
            | "_stack_top"
            | "_stack_bottom"
            | "_kernel_start"
            | "_kernel_end"
            | "__heap_start"
            | "__heap_end"
            | "__global_pointer$"
    ) || (sym == "spl_start"
        && defined.iter().any(|defined_sym| {
            defined_sym == "spl_start" || defined_sym.ends_with("__spl_start") || defined_sym.ends_with("___start")
        }))
}

fn has_equivalent_defined_symbol(sym: &str, defined: &std::collections::HashSet<String>) -> bool {
    if defined.contains(sym) {
        return true;
    }
    if sym.contains("_dot_") {
        return defined.contains(&sym.replace("_dot_", "."));
    }
    if sym.contains('.') {
        return defined.contains(&sym.replace('.', "_dot_"));
    }
    false
}

fn is_optional_weak_hook_symbol(sym: &str) -> bool {
    matches!(
        sym,
        "spl_main"
            | "rt_set_args"
            | "__simple_runtime_init"
            | "__simple_runtime_shutdown"
            | "__simple_call_module_inits"
    )
}

/// Return true for runtime-lifecycle symbols emitted by the compiler's own
/// generated link objects rather than by external libraries.
///
/// `__simple_call_module_inits` is emitted with a real body by the init-caller
/// object (see `generate_init_caller`), and `__simple_runtime_init` /
/// `__simple_runtime_shutdown` are declared `__attribute__((weak))` in the
/// generated `_main_stub` and called only behind `if (sym) sym();` null-guards.
/// All three become resolvable (or safely NULL) at the final link, but the
/// stub-classification pass runs before those generated objects are in the link
/// set, so they appear undefined here. Exempt them so they are not counted as
/// "needs stub".
///
/// Mach-O prepends an extra leading underscore (`___simple_runtime_init`), so we
/// also check the once-stripped form (matching `is_system_symbol`'s convention).
fn is_compiler_provided_runtime_symbol(sym: &str) -> bool {
    fn matches_bare(name: &str) -> bool {
        name.starts_with("__simple_runtime_") || name == "__simple_call_module_inits"
    }
    let stripped = sym.strip_prefix('_').unwrap_or(sym);
    matches_bare(sym) || matches_bare(stripped)
}

fn is_runtime_owned_symbol(sym: &str) -> bool {
    sym.trim_start_matches('_').starts_with("rt_")
}

/// Escape hatch for the undefined-runtime-symbol verdict below. Named
/// separately from `linker/native_binary/stubs.rs`'s `SIMPLE_ALLOW_UNRESOLVED_RT`
/// so the two linker lanes can be bypassed independently.
pub(crate) const ALLOW_UNRESOLVED_RUNTIME_ENV: &str = "SIMPLE_ALLOW_UNRESOLVED_RUNTIME";

/// True for a symbol owned by the runtime rather than by application code.
///
/// `src/runtime/runtime.h` exports exactly two prefixes: `rt_` (802 declarations)
/// and `spl_` (99). Both are runtime property; an undefined reference to either
/// is a missing runtime implementation, never an optional application function.
/// Mach-O's extra leading underscore is stripped, matching `is_system_symbol`.
fn is_runtime_prefixed_symbol(sym: &str) -> bool {
    let bare = sym.trim_start_matches('_');
    bare.starts_with("rt_") || bare.starts_with("spl_")
}

/// Runtime symbols that are GENUINELY optional -- a build may legitimately link
/// without them because every call site is null-guarded or the symbol is a hook
/// supplied only by some hosts.
///
/// This is the allowlist mechanism for the fail-closed check. Adding a name here
/// is a claim that a NULL definition is CORRECT, not merely tolerable. Names that
/// are simply not implemented yet do NOT belong here -- implement them, or run
/// the bootstrap lane, which is exempt wholesale.
const RT_OPTIONAL_SYMBOLS: &[&str] = &[
    // Set only by hosts that pass argv through; call sites are `if (sym) sym();`.
    "rt_set_args",
];

fn is_runtime_optional_symbol(sym: &str) -> bool {
    let bare = sym.trim_start_matches('_');
    RT_OPTIONAL_SYMBOLS.contains(&bare)
}

fn alias_gc_prelude(os: TargetOS) -> &'static str {
    if os == TargetOS::MacOS {
        ".subsections_via_symbols\n"
    } else {
        ""
    }
}

fn alias_gc_section(os: TargetOS, index: usize) -> String {
    match os {
        TargetOS::MacOS => String::new(),
        TargetOS::Windows => format!(".section .text$stub_{index},\"xr\"\n"),
        _ => format!(".section .text.stub_{index},\"ax\",@progbits\n"),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FreestandingUnresolvedMode {
    DeferToLinker,
    StrictPrecheck,
    EmitStubs,
}

fn freestanding_unresolved_mode() -> FreestandingUnresolvedMode {
    let no_stub_fallback = std::env::var("SIMPLE_NO_STUB_FALLBACK").as_deref() == Ok("1");
    let strict_precheck = std::env::var("SIMPLE_STRICT_FREESTANDING_PRECHECK").as_deref() == Ok("1");

    // The strict no-fallback contract is authoritative. Some legacy OS build
    // profiles still export SIMPLE_ALLOW_FREESTANDING_STUBS=1; allowing that
    // opt-in to win here silently fabricated weak return-zero definitions even
    // when the caller explicitly required a stub-free build. Defer by default
    // so section GC can discard dead references, or preserve the explicitly
    // requested eager precheck, but never enter EmitStubs.
    if no_stub_fallback {
        if strict_precheck {
            FreestandingUnresolvedMode::StrictPrecheck
        } else {
            FreestandingUnresolvedMode::DeferToLinker
        }
    } else if std::env::var("SIMPLE_ALLOW_FREESTANDING_STUBS").as_deref() == Ok("1") {
        FreestandingUnresolvedMode::EmitStubs
    } else if strict_precheck {
        FreestandingUnresolvedMode::StrictPrecheck
    } else {
        FreestandingUnresolvedMode::DeferToLinker
    }
}

// ---------------------------------------------------------------------------
// Fabricated-stub ratchet
//
// This guards ONE of the TWO fabrication sites: the FREESTANDING one
// (`generate_stub_object_freestanding`). The hosted twin `generate_stub_object`
// is a separate site that this ratchet has never seen -- it emits ASSEMBLY, not
// C, and its bodies return the TAGGED-NIL sentinel 3, not 0 (see
// `asm_helpers::asm_ret_nil`: `movq $3, %rax; retq`). Do not read the wording
// below as covering that path. It is now fail-closed on its own terms via
// SIMPLE_ALLOW_INTERNAL_STUBS.
//
// The weak nil-returning C bodies emitted below in THIS freestanding path
// (`__attribute__((weak)) __stub_i64 {wrap}(void) { return 0; }`) are the mechanism that once shipped a
// nil-returning `rt_array_copy` into a guest and silently shredded every array
// copy nine steps downstream.
//
// Unlike a post-link disassembly guard, this channel needs no classifier and
// can produce no false positives: it does not decide whether a body looks
// fabricated, it reports exactly the set of symbols this function is itself
// about to fabricate.
//
// The ratchet is per-entry and NEW-ONLY: existing debt is recorded in
// `config/freestanding_fabricated_stub_baseline.sdn` and does not fail the
// build, because the production freestanding link currently cannot link
// without these stubs. A symbol that is NOT in the entry's baseline fails the
// link.
// ---------------------------------------------------------------------------

/// Default location of the fabricated-stub baseline, overridable for tests.
fn fabricated_stub_baseline_path(project_root: &Path) -> PathBuf {
    if let Ok(p) = std::env::var("SIMPLE_FABRICATED_STUB_BASELINE") {
        if !p.is_empty() {
            return PathBuf::from(p);
        }
    }
    project_root.join("config/freestanding_fabricated_stub_baseline.sdn")
}

/// Per-entry baseline key: the output binary's basename.
///
/// Deliberately identical to `simpleos_entry_key` in
/// `src/compiler/70.backend/backend/llvm_native_link.spl`, so the two baseline
/// files key their rows the same way.
fn fabricated_stub_entry_key(output: &Path) -> String {
    output
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| output.to_string_lossy().to_string())
}

/// Parse `<entry-key> <symbol>` rows. `#` starts a comment; blank lines are
/// skipped. A malformed row is a hard error -- silently degrading to an empty
/// baseline would be a fail-open on the exact channel this file gates.
fn parse_fabricated_stub_baseline(text: &str) -> Result<std::collections::BTreeSet<(String, String)>, String> {
    let mut rows = std::collections::BTreeSet::new();
    for (lineno, raw) in text.lines().enumerate() {
        let line = match raw.find('#') {
            Some(i) => &raw[..i],
            None => raw,
        };
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() != 2 {
            return Err(format!(
                "fabricated-stub baseline line {}: expected `<entry-key> <symbol>`, got {:?}",
                lineno + 1,
                line
            ));
        }
        rows.insert((parts[0].to_string(), parts[1].to_string()));
    }
    Ok(rows)
}

/// Rewrite the rows for one entry, preserving comments and every other entry.
///
/// This IS the documented regeneration procedure
/// (`SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1`), so the procedure recorded in
/// the baseline file cannot drift from what the code does.
fn rewrite_fabricated_stub_baseline(existing: &str, entry_key: &str, symbols: &[String]) -> String {
    let mut out = String::new();
    for raw in existing.lines() {
        let code = match raw.find('#') {
            Some(i) => &raw[..i],
            None => raw,
        };
        let first = code.split_whitespace().next();
        if first == Some(entry_key) {
            continue; // replaced below
        }
        out.push_str(raw);
        out.push('\n');
    }
    if !out.ends_with("\n\n") && !out.is_empty() {
        out.push('\n');
    }
    for sym in symbols {
        out.push_str(entry_key);
        out.push(' ');
        out.push_str(sym);
        out.push('\n');
    }
    out
}

/// Split the fabricated set into (already-baselined, NEW) for one entry.
fn partition_fabricated_against_baseline(
    rows: &std::collections::BTreeSet<(String, String)>,
    entry_key: &str,
    fabricated: &[String],
) -> (Vec<String>, Vec<String>) {
    let mut known = Vec::new();
    let mut new_syms = Vec::new();
    for sym in fabricated {
        if rows.contains(&(entry_key.to_string(), sym.clone())) {
            known.push(sym.clone());
        } else {
            new_syms.push(sym.clone());
        }
    }
    (known, new_syms)
}

/// Report every symbol about to be weak-stubbed, and fail on NEW ones.
///
/// Reporting is unconditional and names every symbol: silence is the defect
/// this guard exists to remove.
fn check_fabricated_stub_ratchet(project_root: &Path, output: &Path, fabricated: &[String]) -> Result<(), String> {
    let entry_key = fabricated_stub_entry_key(output);
    let baseline_path = fabricated_stub_baseline_path(project_root);
    let existing = std::fs::read_to_string(&baseline_path).unwrap_or_default();
    let rows = parse_fabricated_stub_baseline(&existing)
        .map_err(|e| format!("{} ({})", e, baseline_path.display()))?;
    let entry_baselined = rows.iter().any(|(k, _)| k == &entry_key);
    let (known, new_syms) = partition_fabricated_against_baseline(&rows, &entry_key, fabricated);

    eprintln!(
        "Fabricated freestanding stubs: {} symbol(s) for entry '{}' -- weak bodies that RETURN 0 \
         (baseline {}: {} known, {} new)",
        fabricated.len(),
        entry_key,
        baseline_path.display(),
        known.len(),
        new_syms.len()
    );
    for sym in &known {
        eprintln!("  FABRICATED     {} {}", entry_key, sym);
    }
    for sym in &new_syms {
        eprintln!("  FABRICATED-NEW {} {}", entry_key, sym);
    }

    if std::env::var("SIMPLE_FABRICATED_STUB_BASELINE_WRITE").as_deref() == Ok("1") {
        let updated = rewrite_fabricated_stub_baseline(&existing, &entry_key, fabricated);
        if let Some(parent) = baseline_path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        std::fs::write(&baseline_path, updated)
            .map_err(|e| format!("write fabricated-stub baseline {}: {e}", baseline_path.display()))?;
        eprintln!(
            "Fabricated-stub baseline REWRITTEN for entry '{}': {} row(s) -> {}",
            entry_key,
            fabricated.len(),
            baseline_path.display()
        );
        return Ok(());
    }

    if !entry_baselined {
        // A never-measured entry has no debt record. Failing here would break
        // every freestanding entry that has not been baselined yet, so this
        // reports loudly instead -- escalate with the strict env var.
        let msg = format!(
            "fabricated-stub baseline has NO rows for entry '{}'; {} symbol(s) fabricated unmeasured. \
             Baseline it with SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1 on this exact build.",
            entry_key,
            fabricated.len()
        );
        if std::env::var("SIMPLE_STRICT_FABRICATED_STUB_RATCHET").as_deref() == Ok("1") {
            return Err(msg);
        }
        eprintln!("WARNING: {}", msg);
        return Ok(());
    }

    if !new_syms.is_empty() {
        return Err(format!(
            "freestanding link would FABRICATE {} symbol(s) not in the baseline for entry '{}': {}. \
             These get weak bodies that return 0 on this freestanding path (the hosted \
             path returns the tagged-nil sentinel 3 instead), which silently corrupts every caller. \
             Implement them, or -- only if nil is genuinely the correct answer -- re-baseline with \
             SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1 and justify it in {}.",
            new_syms.len(),
            entry_key,
            new_syms.join(", "),
            baseline_path.display()
        ));
    }
    Ok(())
}

fn resolve_defined_suffix_alias(sym: &str, defined: &std::collections::HashSet<String>) -> Option<String> {
    if is_runtime_owned_symbol(sym) {
        return None;
    }

    let sanitized = sym.replace('.', "_dot_");
    let unique_suffix = |suffix: &str| {
        let mut matches = defined
            .iter()
            .filter(|candidate| candidate.as_str() != sym)
            .filter(|candidate| candidate.replace('.', "_dot_").ends_with(suffix));
        let first = matches.next().cloned();
        if matches.next().is_none() {
            first
        } else {
            None
        }
    };

    if sanitized.contains("__") {
        if let Some(exact_module_match) = unique_suffix(&format!("__{}", sanitized)) {
            return Some(exact_module_match);
        }
        if let Some(decorated) = sanitized.strip_prefix('_') {
            return unique_suffix(&format!("__{}", decorated));
        }
        return None;
    }

    let tail = sanitized.rsplit("__").next().unwrap_or(sanitized.as_str());
    unique_suffix(&format!("__{}", tail)).or_else(|| {
        tail.strip_prefix('_')
            .and_then(|decorated| unique_suffix(&format!("__{}", decorated)))
    })
}

/// The bare Simple function name of a mangled pure-Simple module symbol.
///
/// Pure-Simple symbols are mangled `<module_prefix>__<fn_name>` where the module
/// prefix itself uses `__` as its path separator (`lib__common__text__trim`), so
/// the function name is everything after the LAST `__`. Returns `None` for any
/// symbol that is not a pure-Simple module symbol (notably every `rt_*` extern,
/// which this check must not disturb).
pub(crate) fn simple_module_symbol_tail(sym: &str) -> Option<&str> {
    if !(sym.starts_with("lib__") || sym.starts_with("os__")) {
        return None;
    }
    let tail = sym.rsplit("__").next()?;
    if tail.is_empty() {
        None
    } else {
        Some(tail)
    }
}

/// Report undefined pure-Simple module symbols that are defined in the same link
/// under a different module prefix — the stale-object-cache signature.
///
/// Low false positive by construction: a dangling `lib__A__f` reference is a
/// defect in every case (it can only ever become a fabricated nil stub), and the
/// presence of a live `lib__B__f` in the same link names the module it moved to.
fn stale_module_move_report(
    needs_stub: &[String],
    defined: &std::collections::HashSet<String>,
) -> Option<String> {
    use std::collections::HashMap;

    // tail -> defined mangled symbols sharing that bare function name.
    let mut defined_by_tail: HashMap<&str, Vec<&str>> = HashMap::new();
    for sym in defined {
        if let Some(tail) = simple_module_symbol_tail(sym) {
            defined_by_tail.entry(tail).or_default().push(sym.as_str());
        }
    }

    let mut findings: Vec<String> = Vec::new();
    for sym in needs_stub {
        let Some(tail) = simple_module_symbol_tail(sym) else {
            continue;
        };
        let Some(providers) = defined_by_tail.get(tail) else {
            continue;
        };
        let mut elsewhere: Vec<&str> = providers
            .iter()
            .copied()
            .filter(|candidate| *candidate != sym.as_str())
            .collect();
        if elsewhere.is_empty() {
            continue;
        }
        elsewhere.sort_unstable();
        findings.push(format!("  {sym}\n      moved to: {}", elsewhere.join(", ")));
    }

    if findings.is_empty() {
        return None;
    }
    findings.sort();
    Some(format!(
        "stale object cache detected: {} undefined pure-Simple module symbol(s) are \
defined in this same link under a different module prefix.\n{}\n\
This means a cached object compiled against the OLD provider module was reused \
after the function moved modules. Linking it would fabricate a weak nil stub for \
the dead name and every call site would silently return nil (0 on the freestanding \
path, the tagged-nil sentinel 3 on the hosted path)/false.\n\
Fix: rebuild with a clean object cache (--clean, or delete the native cache \
objects directory). If this survives a clean build the reference is genuinely \
dangling and the source must be repaired.",
        findings.len(),
        findings.join("\n")
    ))
}

/// Generate a legacy stub object file for a FREESTANDING (cross) target.
///
/// Unlike `generate_stub_object`, this does not emit asm using host instructions
/// and does not scan host system libraries. It discovers unresolved symbols across
/// the provided `object_paths` (and any boot objects), filters out symbols defined
/// elsewhere in that same object set. By default this now defers unresolved
/// enforcement to the real linker, which can apply section GC and report only
/// live failures. Set `SIMPLE_STRICT_FREESTANDING_PRECHECK=1` to restore the old
/// eager-failure mode, or `SIMPLE_ALLOW_FREESTANDING_STUBS=1` to emit weak
/// legacy stubs while debugging incomplete ports.
pub(crate) fn generate_stub_object_freestanding(
    temp_dir: &Path,
    object_paths: &[PathBuf],
    boot_objects: &[PathBuf],
    triple: &str,
    march: &str,
    mabi: &str,
    project_root: &Path,
    output: &Path,
) -> Result<Option<PathBuf>, String> {
    use std::collections::{BTreeSet, HashSet};

    fn scan_nm_defined_undefined(path: &Path) -> Option<(HashSet<String>, BTreeSet<String>)> {
        let output = nm_command().arg("-g").arg("-p").arg(path).output().ok()?;
        if !output.status.success() {
            return None;
        }
        let mut defined = HashSet::new();
        let mut undefined = BTreeSet::new();
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert((*name).to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert((*name).to_string());
                }
                _ => {}
            }
        }
        Some((defined, undefined))
    }

    let mut defined: HashSet<String> = HashSet::new();
    let mut undefined: BTreeSet<String> = BTreeSet::new();

    // Scan both Simple object_paths AND any boot_objects (boot .c/.s may define
    // or reference symbols that must not be stubbed over).
    let scan_paths: Vec<PathBuf> = object_paths.iter().chain(boot_objects.iter()).cloned().collect();
    let worker_count = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    if worker_count <= 1 || scan_paths.len() < 16 {
        for path in &scan_paths {
            if let Some((local_defined, local_undefined)) = scan_nm_defined_undefined(path) {
                defined.extend(local_defined);
                undefined.extend(local_undefined);
            }
        }
    } else {
        let chunk_size = scan_paths.len().div_ceil(worker_count);
        let mut handles = Vec::new();
        for chunk in scan_paths.chunks(chunk_size.max(1)) {
            let chunk_paths = chunk.to_vec();
            handles.push(std::thread::spawn(move || {
                let mut local_defined = HashSet::new();
                let mut local_undefined = BTreeSet::new();
                for path in &chunk_paths {
                    if let Some((defined, undefined)) = scan_nm_defined_undefined(path) {
                        local_defined.extend(defined);
                        local_undefined.extend(undefined);
                    }
                }
                (local_defined, local_undefined)
            }));
        }
        for handle in handles {
            if let Ok((local_defined, local_undefined)) = handle.join() {
                defined.extend(local_defined);
                undefined.extend(local_undefined);
            }
        }
    }

    // Only stub symbols that are genuinely unresolved in the link set.
    // Exclude obvious system/dyld/C++ runtime mangled names.
    let needs_stub: Vec<String> = undefined
        .into_iter()
        .filter(|s| !has_equivalent_defined_symbol(s, &defined))
        .filter(|s| !s.is_empty())
        .filter(|s| {
            s.chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.')
        })
        .filter(|s| !s.starts_with("_dyld_"))
        .filter(|s| !s.starts_with("_ZSt") && !s.starts_with("_ZNSt"))
        .filter(|s| !is_system_symbol(s))
        .filter(|s| !is_compiler_rt_builtin_symbol(s))
        .filter(|s| !is_linker_provided_symbol(s, &defined))
        .filter(|s| s != "main" && s != "_main")
        .collect();

    // Stale-object-cache consistency check (runs BEFORE the unresolved-mode
    // match, so `DeferToLinker` / `EmitStubs` cannot swallow it).
    //
    // An undefined `lib__*` / `os__*` symbol whose bare function name IS defined
    // in this very same link under a DIFFERENT module prefix is unambiguous
    // evidence that a cached object compiled against the OLD provider module
    // survived a cross-module symbol move. Left alone, the stub generator
    // fabricates an 8-byte weak nil body for the dead name and every call site
    // in the stale object silently receives 0/false with no link error — the
    // same fail-open shape as a nil-returning `rt_*` stub.
    //
    // This is a cheap backstop for the dependency-aware object cache key
    // (`cross_module_layout_fingerprint` in `native_project::mod`): it catches
    // the class even if a future key change regresses. It deliberately does NOT
    // touch the `rt_*` channels.
    if let Some(report) = stale_module_move_report(&needs_stub, &defined) {
        return Err(report);
    }

    let mut compat_symbols = BTreeSet::new();
    let mut unresolved = Vec::new();
    for sym in needs_stub {
        match sym.as_str() {
            "i64.max" | "i64.min" | "str.repeat" | "bytes_to_u16_le" | "bytes_to_u16_be" | "bytes_to_u32_le"
            | "bytes_to_u32_be" | "rt_str_hash" | "rt_range" | "rt_value_bool" | "rt_unwrap_or_self" | "rt_is_none"
            | "rt_is_some" => {
                compat_symbols.insert(sym);
            }
            _ => unresolved.push(sym),
        }
    }

    eprintln!(
        "Freestanding unresolved symbol check: {} unexpected symbol(s)",
        unresolved.len() + compat_symbols.len()
    );
    if std::env::var("SIMPLE_TRACE_STUBS").is_ok() {
        for s in unresolved.iter().chain(compat_symbols.iter()).take(20) {
            eprintln!("  STUB: {}", s);
        }
        let total = unresolved.len() + compat_symbols.len();
        if total > 20 {
            eprintln!("  ... ({} more)", total - 20);
        }
    }

    if unresolved.is_empty() && compat_symbols.is_empty() {
        return Ok(None);
    }
    let unresolved_mode = freestanding_unresolved_mode();
    match unresolved_mode {
        FreestandingUnresolvedMode::DeferToLinker => {
            eprintln!(
                "Freestanding unresolved precheck deferred to linker: {} candidate symbol(s)",
                unresolved.len()
            );
            if compat_symbols.is_empty() {
                return Ok(None);
            }
        }
        FreestandingUnresolvedMode::StrictPrecheck => {
            if unresolved.is_empty() {
                // Only compatibility aliases remain; emit them below rather than
                // failing the precheck on an empty unresolved set.
            } else {
                return Err(format!(
                    "freestanding link has unexpected unresolved symbol(s): {}",
                    unresolved.join(", ")
                ));
            }
        }
        FreestandingUnresolvedMode::EmitStubs => {}
    }

    let stub_c = temp_dir.join("_stubs_freestanding.c");
    let mut code = String::from("/* Auto-generated freestanding stubs — weak definitions return 0 */\n");
    code.push_str("typedef long long __stub_i64;\n\n");
    if compat_symbols.contains("str.repeat") {
        code.push_str(
            "__stub_i64 lib__common__string_core__str_repeat(__stub_i64, __stub_i64);\n\
             __stub_i64 __stub_compat_str_repeat(__stub_i64 s, __stub_i64 count) __asm__(\"str.repeat\");\n\
             __stub_i64 __stub_compat_str_repeat(__stub_i64 s, __stub_i64 count) {\n\
                 return lib__common__string_core__str_repeat(s, count);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("i64.max") {
        code.push_str(
            "__stub_i64 __stub_compat_i64_max(__stub_i64 a, __stub_i64 b) __asm__(\"i64.max\");\n\
             __stub_i64 __stub_compat_i64_max(__stub_i64 a, __stub_i64 b) {\n\
                 return a >= b ? a : b;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("i64.min") {
        code.push_str(
            "__stub_i64 __stub_compat_i64_min(__stub_i64 a, __stub_i64 b) __asm__(\"i64.min\");\n\
             __stub_i64 __stub_compat_i64_min(__stub_i64 a, __stub_i64 b) {\n\
                 return a <= b ? a : b;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u16_le") {
        code.push_str(
            "unsigned short __stub_compat_bytes_to_u16_le(unsigned char b0, unsigned char b1) __asm__(\"bytes_to_u16_le\");\n\
             unsigned short __stub_compat_bytes_to_u16_le(unsigned char b0, unsigned char b1) {\n\
                 return (unsigned short)(((unsigned short)b1 << 8) | (unsigned short)b0);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u16_be") {
        code.push_str(
            "unsigned short __stub_compat_bytes_to_u16_be(unsigned char b0, unsigned char b1) __asm__(\"bytes_to_u16_be\");\n\
             unsigned short __stub_compat_bytes_to_u16_be(unsigned char b0, unsigned char b1) {\n\
                 return (unsigned short)(((unsigned short)b0 << 8) | (unsigned short)b1);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u32_le") {
        code.push_str(
            "unsigned int __stub_compat_bytes_to_u32_le(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) __asm__(\"bytes_to_u32_le\");\n\
             unsigned int __stub_compat_bytes_to_u32_le(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) {\n\
                 return ((unsigned int)b0) | ((unsigned int)b1 << 8) | ((unsigned int)b2 << 16) | ((unsigned int)b3 << 24);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u32_be") {
        code.push_str(
            "unsigned int __stub_compat_bytes_to_u32_be(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) __asm__(\"bytes_to_u32_be\");\n\
             unsigned int __stub_compat_bytes_to_u32_be(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) {\n\
                 return ((unsigned int)b3) | ((unsigned int)b2 << 8) | ((unsigned int)b1 << 16) | ((unsigned int)b0 << 24);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_str_hash") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_str_hash(__stub_i64 s) __asm__(\"rt_str_hash\");\n\
             __stub_i64 __stub_compat_rt_str_hash(__stub_i64 s) {\n\
                 const unsigned long long offset = 14695981039346656037ULL;\n\
                 const unsigned long long prime = 1099511628211ULL;\n\
                 const unsigned char* p = (const unsigned char*)(unsigned long long)s;\n\
                 unsigned long long h = offset;\n\
                 if (!p) {\n\
                     return (__stub_i64)h;\n\
                 }\n\
                 while (*p) {\n\
                     h ^= (unsigned long long)(*p++);\n\
                     h *= prime;\n\
                 }\n\
                 return (__stub_i64)h;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_range") {
        code.push_str(
            "__stub_i64 rt_array_new(__stub_i64 cap);\n\
             signed char rt_array_push(__stub_i64 arr, __stub_i64 val);\n\
             __stub_i64 __stub_compat_rt_range(__stub_i64 start, __stub_i64 end) __asm__(\"rt_range\");\n\
             __stub_i64 __stub_compat_rt_range(__stub_i64 start, __stub_i64 end) {\n\
                 if (end <= start) return rt_array_new(0);\n\
                 __stub_i64 result = rt_array_new(end - start);\n\
                 if (result == 3) return result;\n\
                 for (__stub_i64 value = start; value < end; value++) {\n\
                     (void)rt_array_push(result, value << 3);\n\
                 }\n\
                 return result;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_value_bool") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_value_bool(unsigned char b) __asm__(\"rt_value_bool\");\n\
             __stub_i64 __stub_compat_rt_value_bool(unsigned char b) {\n\
                return b ? 11 : 19;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_unwrap_or_self") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_unwrap_or_self(__stub_i64 val) __asm__(\"rt_unwrap_or_self\");\n\
             __stub_i64 __stub_compat_rt_unwrap_or_self(__stub_i64 val) {\n\
                 if (val == 3) return 3;\n\
                 if ((((unsigned long long)val) & 0x7ULL) != 0x1ULL) return val;\n\
                 __stub_i64* p = (__stub_i64*)((((unsigned long long)val) & ~0x7ULL));\n\
                 if (!p) return val;\n\
                 if (((unsigned int)p[0]) != 7U) return val;\n\
                 return p[2] == 3 ? val : p[2];\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_is_none") || compat_symbols.contains("rt_is_some") {
        code.push_str(
            "static __stub_i64 __stub_compat_rt_is_none_value(__stub_i64 val) {\n\
                 if (val == 3) return 1;\n\
                 if ((((unsigned long long)val) & 0x7ULL) != 0x1ULL) return 0;\n\
                 __stub_i64* p = (__stub_i64*)((((unsigned long long)val) & ~0x7ULL));\n\
                 if (!p) return 0;\n\
                 if (((unsigned int)p[0]) != 7U) return 0;\n\
                 return p[2] == 3 ? 1 : 0;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_is_none") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_is_none(__stub_i64 val) __asm__(\"rt_is_none\");\n\
             __stub_i64 __stub_compat_rt_is_none(__stub_i64 val) {\n\
                 return __stub_compat_rt_is_none_value(val);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_is_some") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_is_some(__stub_i64 val) __asm__(\"rt_is_some\");\n\
             __stub_i64 __stub_compat_rt_is_some(__stub_i64 val) {\n\
                 return __stub_compat_rt_is_none_value(val) ? 0 : 1;\n\
             }\n\n",
        );
    }
    if matches!(unresolved_mode, FreestandingUnresolvedMode::EmitStubs) {
        // Guard at the fabrication site: report every symbol about to get a
        // weak nil-returning body, and fail on any that is not baselined debt.
        check_fabricated_stub_ratchet(project_root, output, &unresolved)?;
        for (i, sym) in unresolved.iter().enumerate() {
            // Sanitize C identifier for the wrapper name; keep the external symbol
            // name exact via an __asm__ label so the linker sees the mangled form.
            let wrapper = format!("__stub_fs_{}", i);
            code.push_str(&format!(
                "__attribute__((weak)) __stub_i64 {wrap}(void) __asm__(\"{sym}\");\n\
                 __attribute__((weak)) __stub_i64 {wrap}(void) {{ return 0; }}\n\n",
                wrap = wrapper,
                sym = sym
            ));
        }
    }

    std::fs::write(&stub_c, &code).map_err(|e| format!("write freestanding stubs: {e}"))?;

    let stub_o = temp_dir.join("_stubs_freestanding.o");
    let cc = find_c_compiler();
    let compilers: Vec<String> = {
        let mut v = vec![];
        #[cfg(target_os = "macos")]
        for p in [
            "/opt/homebrew/opt/llvm@18/bin/clang",
            "/opt/homebrew/opt/llvm/bin/clang",
            "/usr/local/opt/llvm/bin/clang",
        ] {
            if std::path::Path::new(p).exists() && !v.contains(&p.to_string()) {
                v.push(p.to_string());
            }
        }
        if !v.contains(&cc) {
            v.push(cc.clone());
        }
        v
    };

    let mut last_stderr = String::new();
    for compiler in &compilers {
        let mut cmd = std::process::Command::new(compiler);
        cmd.args(["-c", "-ffreestanding", "-nostdlib", "-fno-pie"])
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .arg(format!("--target={}", triple));
        if triple.contains("x86_64") {
            cmd.arg("-mno-red-zone");
        }
        if !march.is_empty() {
            cmd.arg(march);
        }
        if !mabi.is_empty() {
            cmd.arg(mabi);
        }
        // For RISC-V, medany needed for freestanding.
        if march.contains("rv") {
            cmd.arg("-mcmodel=medany");
        }

        let output = cmd
            .output()
            .map_err(|e| format!("compile freestanding stubs ({compiler}): {e}"))?;
        if output.status.success() {
            return Ok(Some(stub_o));
        }
        last_stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    }
    Err(format!("failed to compile freestanding stubs: {}", last_stderr))
}

/// Generate a stub object file that provides weak definitions for all unresolved symbols.
#[cfg(any(
    target_os = "android",
    target_os = "ios",
    target_os = "macos",
    target_os = "freebsd",
    target_os = "linux",
    target_os = "windows"
))]
pub(crate) fn generate_stub_object(
    temp_dir: &std::path::Path,
    object_paths: &[PathBuf],
    main_o: &std::path::Path,
    selected_runtime_libs: &[&std::path::Path],
    imports: &ModuleImports,
) -> Result<PathBuf, String> {
    use std::collections::{HashSet, BTreeSet};

    let mut defined = HashSet::new();
    let mut undefined = BTreeSet::new();

    let archive_path = temp_dir.join("libspl_objects.a");
    let scan_paths: Vec<&std::path::Path> = if archive_path.exists() {
        vec![archive_path.as_path(), main_o]
    } else {
        let mut v: Vec<&std::path::Path> = object_paths.iter().map(|p| p.as_path()).collect();
        v.push(main_o);
        v
    };

    for path in &scan_paths {
        let output = nm_command()
            .arg("-g")
            .arg("-p")
            .arg(path)
            .output()
            .map_err(|e| format!("nm: {e}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert(name.to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert(name.to_string());
                }
                _ => {}
            }
        }
    }

    let fallback_runtime = if selected_runtime_libs.is_empty() {
        find_runtime_library()
    } else {
        None
    };
    let runtime_libs: Vec<&std::path::Path> = if let Some(path) = fallback_runtime.as_deref() {
        vec![path]
    } else {
        selected_runtime_libs.to_vec()
    };
    for rt_path in runtime_libs {
        let output = nm_command()
            .arg("-g")
            .arg("-p")
            .arg(rt_path)
            .output()
            .map_err(|e| format!("nm runtime: {e}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert(name.to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert(name.to_string());
                }
                _ => {}
            }
        }
    }

    let plat_config = simple_common::platform::link_config::PlatformLinkConfig::for_host();
    for lib_path in &plat_config.system_scan_libs {
        if std::path::Path::new(lib_path).exists() {
            let mut nm_cmd = nm_command();
            for flag in &plat_config.nm_flags {
                nm_cmd.arg(flag);
            }
            nm_cmd.arg(lib_path);
            if let Ok(output) = nm_cmd.output() {
                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if let [_addr, sym_type, name] = parts.as_slice() {
                        if *sym_type != "U" {
                            let base = name.split("@@").next().unwrap_or(name);
                            defined.insert(base.to_string());
                            if base != *name {
                                defined.insert(name.to_string());
                            }
                        }
                    }
                }
            }
        }
    }

    // LOAD milestone (see memory: simple-bootstrap-stage4-runtime-symbol-gap):
    // the self-hosted bootstrap runtime is intentionally incomplete — some rt_*
    // helpers (rt_array_filter/all/any, rt_value_*, rt_any_add, ...) are not yet
    // implemented under the names codegen emits. Normally rt_* are excluded from
    // stubbing (is_runtime_owned_symbol) because the runtime owns them; under
    // bootstrap we weak-stub the genuinely-undefined ones (those absent from
    // `defined`, i.e. not provided by any linked archive) so the binary can LOAD
    // and run programs that don't exercise them. Real implementations replace
    // these stubs incrementally. No effect on complete-runtime builds: there are
    // no undefined rt_* to stub there.
    let stub_missing_runtime = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1")
        || std::env::var("SIMPLE_STUB_MISSING_RT").as_deref() == Ok("1");

    // FAIL CLOSED on undefined RUNTIME-owned symbols (task: 2026-08-21).
    //
    // `is_runtime_owned_symbol` deliberately keeps `rt_*` out of `needs_stub` --
    // the runtime, not the stub generator, owns them. Until now that was the END
    // of the story: the reference was simply left undefined and the final link
    // tolerated it, leaving a NULL GOT slot. `rt_unwrap_or_trap` reached every
    // self-hosted stage binary that way and SEGV'd on a three-line hello world
    // while `--version` answered cleanly. A symbol nobody defines is not
    // "optional", it is a call through address 0.
    //
    // This turns that silent tolerance into a verdict that NAMES the symbols.
    // Genuinely optional externs stay tolerated through `RT_OPTIONAL_SYMBOLS`
    // below (the allowlist mechanism, mirroring RT_KEEP in
    // `linker/native_binary/stubs.rs`, which is the same policy on the other
    // linker lane). Bootstrap/stub-missing-runtime lanes are exempt: they
    // deliberately weak-stub the gap so the binary can LOAD.
    let undefined_runtime: Vec<String> = undefined
        .iter()
        .filter(|s| !defined.contains(*s))
        .filter(|s| is_runtime_prefixed_symbol(s))
        .filter(|s| !is_optional_weak_hook_symbol(s))
        .filter(|s| !is_compiler_provided_runtime_symbol(s))
        .filter(|s| !is_linker_provided_symbol(s, &defined))
        .filter(|s| !is_system_symbol(s))
        .filter(|s| !is_runtime_optional_symbol(s))
        .cloned()
        .collect();
    if !undefined_runtime.is_empty() && !stub_missing_runtime {
        let names = undefined_runtime.join(", ");
        if std::env::var(ALLOW_UNRESOLVED_RUNTIME_ENV).as_deref() == Ok("1") {
            eprintln!(
                "Warning: {} runtime symbol(s) are undefined in this link and will be left \
                 unresolved ({}=1 set): {}",
                undefined_runtime.len(),
                ALLOW_UNRESOLVED_RUNTIME_ENV,
                names
            );
        } else {
            return Err(format!(
                "{} runtime symbol(s) referenced by generated code have no definition in any \
linked object, runtime archive, or system library: {}\n\
  The native link tolerates undefined symbols, so this would produce a binary with a NULL \
GOT slot per name and SEGV on the first call -- exactly the failure that made every \
self-hosted stage binary crash on hello world (rt_unwrap_or_trap, 2026-08-21).\n\
  Fix: implement the symbol in the runtime (src/runtime/simple_core/*.spl for the \
simple-core archive, src/runtime/*.c for the C runtime), correct the extern name, add it \
to RT_OPTIONAL_SYMBOLS in pipeline/native_project/stubs.rs if it is genuinely optional, \
or set {}=1 to bypass at your own risk.",
                undefined_runtime.len(),
                names,
                ALLOW_UNRESOLVED_RUNTIME_ENV
            ));
        }
    }

    let mut needs_stub: Vec<String> = undefined
        .into_iter()
        .filter(|s| !defined.contains(s))
        .filter(|s| !s.starts_with("_dyld_") && *s != "_main" && *s != "main")
        .filter(|s| {
            !s.starts_with("_ZSt") && !s.starts_with("_ZNSt") && !s.starts_with("ZSt") && !s.starts_with("ZNSt")
        })
        .filter(|s| !is_optional_weak_hook_symbol(s))
        .filter(|s| !is_compiler_provided_runtime_symbol(s))
        // Inline-asm blocks are concrete compiler output, never optional
        // application functions. Weak-stubbing a block after target-specific
        // asm compilation failed turns a missing instruction path into a
        // false-success binary. Leave the reference for dead stripping or the
        // final linker to diagnose.
        .filter(|s| !is_inline_asm_symbol(s))
        .filter(|s| stub_missing_runtime || !is_runtime_owned_symbol(s))
        .filter(|s| !is_system_symbol(s))
        .filter(|s| !s.starts_with('?') && !s.starts_with("__imp_"))
        .collect();

    let mut simple_symbols = HashSet::new();
    for (raw, mangled_variants) in imports.all_mangled.iter() {
        simple_symbols.insert(raw.clone());
        for mangled in mangled_variants {
            simple_symbols.insert(mangled.clone());
        }
    }
    let internal_missing: Vec<String> = needs_stub
        .iter()
        .filter(|sym| simple_symbols.contains(*sym))
        .cloned()
        .collect();

    let is_bootstrap = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1");
    let strict_no_stub_fallback = std::env::var("SIMPLE_NO_STUB_FALLBACK").as_deref() == Ok("1");
    let is_freestanding = effective_target().os == simple_common::target::TargetOS::None;
    if !is_bootstrap && !strict_no_stub_fallback && !is_freestanding && !internal_missing.is_empty() {
        // FAIL CLOSED. These are Simple-level symbols (including `extern fn`
        // declarations) with no implementation anywhere in the linked object
        // set, the runtime libraries, or the system libraries. This hosted path
        // fabricates ASSEMBLY (`_stubs.s`), not C: `asm_helpers::asm_ret_nil`
        // emits `movq $3, %rax; retq` on x86_64 -- the TAGGED-NIL sentinel 3,
        // not 0. Fabricating that body produced a binary that ran and printed
        // garbage with exit 0 — a silent wrong answer, not a build. The
        // freestanding path guards this with `check_fabricated_stub_ratchet`;
        // this hosted path only ever warned, so the ratchet never saw these
        // symbols. Escape hatch mirrors the freestanding one.
        let allow = std::env::var("SIMPLE_ALLOW_INTERNAL_STUBS").as_deref() == Ok("1");
        let preview = internal_missing.iter().take(12).cloned().collect::<Vec<_>>().join(", ");
        let ellipsis = if internal_missing.len() > 12 { " ..." } else { "" };
        if allow {
            eprintln!(
                "Warning: {} internal Simple symbol(s) will be stubbed: {}{}",
                internal_missing.len(),
                preview,
                ellipsis
            );
        } else {
            return Err(format!(
                "{} internal Simple symbol(s) have no implementation and would be \
fabricated as weak stubs returning the tagged-nil sentinel 3: {}{}\n\
  An `extern fn` (or other Simple declaration) with no definition in any linked \
object, runtime library, or system library cannot be linked into a correct \
binary. Implement the symbol, or set SIMPLE_ALLOW_INTERNAL_STUBS=1 to restore \
the old fabricating behaviour.",
                internal_missing.len(),
                preview,
                ellipsis
            ));
        }
    }

    // The object scan runs before the final linker's section GC, so it also sees
    // references from unreachable functions. Strict mode must still emit
    // compatibility trampolines when the concrete mangled definition is already
    // present; those aliases resolve real code rather than hiding a missing
    // implementation. Leave every genuinely unresolved symbol to the linker.
    if strict_no_stub_fallback {
        needs_stub.retain(|sym| resolve_defined_suffix_alias(sym, &defined).is_some());
    }

    if let Ok(dump_path) = std::env::var("SIMPLE_DUMP_STUBS") {
        let mut all: Vec<String> = needs_stub.to_vec();
        all.sort();
        let contents = if all.is_empty() {
            String::new()
        } else {
            all.join("\n") + "\n"
        };
        std::fs::write(&dump_path, contents).map_err(|e| format!("write stub dump {dump_path}: {e}"))?;
        eprintln!("Wrote {} unresolved symbols to {}", all.len(), dump_path);
    }

    if needs_stub.is_empty() {
        let stub_c = temp_dir.join("_stubs.c");
        std::fs::write(&stub_c, "/* no stubs needed */\n").map_err(|e| format!("write stubs: {e}"))?;
        let stub_o = temp_dir.join("_stubs.o");
        let empty_cc = target_c_compiler(effective_target());
        let status = std::process::Command::new(&empty_cc)
            .arg("-c")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .status()
            .map_err(|e| format!("compile stubs: {e}"))?;
        if !status.success() {
            return Err("failed to compile empty stubs".to_string());
        }
        return Ok(stub_o);
    }

    if strict_no_stub_fallback {
        eprintln!(
            "Generating {} compatibility aliases for resolved symbols...",
            needs_stub.len()
        );
    } else {
        eprintln!(
            "Generating {} stub functions for unresolved symbols...",
            needs_stub.len()
        );
    }
    let preview = needs_stub.iter().take(80).cloned().collect::<Vec<_>>().join(", ");
    eprintln!(
        "{} preview: {}{}",
        if strict_no_stub_fallback {
            "Compatibility alias"
        } else {
            "Unresolved symbol"
        },
        preview,
        if needs_stub.len() > 80 { " ..." } else { "" }
    );
    let forbidden_enum_ctors: Vec<&str> = needs_stub
        .iter()
        .map(|s| s.as_str())
        .filter(|s| matches!(*s, "Some" | "None" | "Ok" | "Err"))
        .collect();
    if !forbidden_enum_ctors.is_empty() {
        return Err(format!(
            "refusing to weak-stub enum short constructors: {}",
            forbidden_enum_ctors.join(", ")
        ));
    }

    let forbidden_core_runtime: Vec<&str> = needs_stub
        .iter()
        .map(|s| s.as_str())
        .filter(|s| {
            matches!(
                *s,
                "rt_enum_new"
                    | "rt_enum_check_discriminant"
                    | "rt_enum_id"
                    | "rt_enum_discriminant"
                    | "rt_enum_payload"
            )
        })
        .collect();
    if !forbidden_core_runtime.is_empty() {
        return Err(format!(
            "refusing to weak-stub core enum runtime symbols: {}",
            forbidden_core_runtime.join(", ")
        ));
    }

    if std::env::var("SIMPLE_TRACE_STUBS").is_ok() {
        for s in &needs_stub {
            eprintln!("  STUB: {}", s);
        }
    }

    #[cfg(target_os = "windows")]
    {
        let mut c_code = String::with_capacity(needs_stub.len() * 120);
        c_code.push_str("/* Auto-generated stubs for bootstrap linking (Windows) */\n");
        c_code.push_str("#include <stdint.h>\n\n");
        for sym in &needs_stub {
            if !plat_config.is_valid_asm_label(sym) {
                continue;
            }
            c_code.push_str(&format!(
                "int64_t __stub_{id}(void) __asm__(\"{sym}\");\n\
                 int64_t __stub_{id}(void) {{ return 3; }}\n\n",
                id = sym.replace('.', "_").replace('$', "_"),
                sym = sym
            ));
        }

        let stub_c = temp_dir.join("_stubs.c");
        std::fs::write(&stub_c, &c_code).map_err(|e| format!("write stubs: {e}"))?;

        let stub_o = temp_dir.join("_stubs.o");
        let stub_cc = std::env::var("CC").unwrap_or_else(|_| "gcc".to_string());
        let output = std::process::Command::new(&stub_cc)
            .arg("-c")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .output()
            .map_err(|e| format!("compile stubs ({stub_cc}): {e}"))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("failed to compile stub functions ({}): {}", stub_cc, stderr));
        }

        return Ok(stub_o);
    }

    #[cfg(not(target_os = "windows"))]
    {
        let mut asm_code = String::with_capacity(needs_stub.len() * 100);
        asm_code.push_str("/* Auto-generated stubs for bootstrap linking */\n");

        let target = effective_target();
        asm_code.push_str(alias_gc_prelude(target.os));
        let ret_nil = simple_common::platform::asm_helpers::asm_ret_nil(&target);
        let jmp_prefix = simple_common::platform::asm_helpers::asm_jmp_instruction(&target);

        for (index, sym) in needs_stub.iter().enumerate() {
            if !plat_config.is_valid_asm_label(sym) {
                continue;
            }
            asm_code.push_str(&alias_gc_section(target.os, index));

            if cfg!(target_os = "macos") && sym.starts_with("___builtin_") {
                let real_fn = format!("_{}", &sym["___builtin_".len()..]);
                asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &real_fn));
                continue;
            }

            if let Some(real_fn) = resolve_defined_suffix_alias(sym, &defined) {
                // Use the platform-aware trampoline emitter so macOS gets
                // `.weak_definition` (its assembler rejects GNU `.weak`).
                asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &real_fn));
                continue;
            }

            let bare = sym.strip_prefix('_').unwrap_or(sym.as_str());
            let rt_sym = format!("_rt_{}", bare);
            if matches!(
                bare,
                "array_len"
                    | "array_new"
                    | "array_get"
                    | "array_set"
                    | "array_append"
                    | "array_push"
                    | "array_pop"
                    | "array_slice"
                    | "array_contains"
                    | "string_new"
                    | "string_len"
                    | "string_concat"
                    | "string_eq"
                    | "string_slice"
                    | "string_char_at"
                    | "string_data"
                    | "string_split"
                    | "string_replace"
                    | "string_find"
                    | "string_rfind"
                    | "alloc"
                    | "free"
                    | "print_str"
                    | "println_str"
                    | "print_value"
                    | "println_value"
            ) && defined.contains(&rt_sym)
            {
                asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &rt_sym));
                continue;
            }

            asm_code.push_str(&plat_config.generate_stub_asm(sym, ret_nil));
        }

        let stub_s = temp_dir.join("_stubs.s");
        std::fs::write(&stub_s, &asm_code).map_err(|e| format!("write stubs: {e}"))?;

        let stub_o = temp_dir.join("_stubs.o");
        let asm_cc = target_c_compiler(effective_target());
        let output = std::process::Command::new(&asm_cc)
            .arg("-c")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_s)
            .output()
            .map_err(|e| format!("assemble stubs ({asm_cc}): {e}"))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("failed to assemble stub functions ({}): {}", asm_cc, stderr));
        }

        Ok(stub_o)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::sync::{Mutex, OnceLock};

    fn freestanding_stub_env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn with_freestanding_stub_env<T>(
        no_fallback: Option<&str>,
        allow: Option<&str>,
        strict: Option<&str>,
        f: impl FnOnce() -> T,
    ) -> T {
        let _guard = freestanding_stub_env_lock().lock().unwrap();
        let names = [
            "SIMPLE_NO_STUB_FALLBACK",
            "SIMPLE_ALLOW_FREESTANDING_STUBS",
            "SIMPLE_STRICT_FREESTANDING_PRECHECK",
        ];
        let previous = names.map(|name| std::env::var(name).ok());
        for (name, value) in names.into_iter().zip([no_fallback, allow, strict]) {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
        let result = f();
        for (name, value) in names.into_iter().zip(previous) {
            match value {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
        result
    }

    #[test]
    fn no_stub_fallback_overrides_freestanding_stub_opt_in() {
        with_freestanding_stub_env(Some("1"), Some("1"), None, || {
            assert_eq!(
                freestanding_unresolved_mode(),
                FreestandingUnresolvedMode::DeferToLinker
            );
        });
        with_freestanding_stub_env(Some("1"), Some("1"), Some("1"), || {
            assert_eq!(
                freestanding_unresolved_mode(),
                FreestandingUnresolvedMode::StrictPrecheck
            );
        });
    }

    #[test]
    fn no_stub_fallback_prevents_freestanding_stub_artifact_creation() {
        use std::process::Command;

        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("unresolved.c");
        let object = dir.path().join("unresolved.o");
        std::fs::write(
            &source,
            "extern long acceptance_missing_symbol(void); long acceptance_probe(void) { return acceptance_missing_symbol(); }\n",
        )
        .unwrap();
        let compile = Command::new("cc")
            .arg("-c")
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .output()
            .unwrap();
        assert!(compile.status.success(), "{}", String::from_utf8_lossy(&compile.stderr));

        let generated = with_freestanding_stub_env(Some("1"), Some("1"), None, || {
            generate_stub_object_freestanding(
                dir.path(),
                std::slice::from_ref(&object),
                &[],
                "aarch64-unknown-none",
                "armv8-a",
                "lp64",
                dir.path(),
                Path::new("acceptance-kernel.elf"),
            )
        })
        .expect("strict no-fallback must defer unresolved symbols to the real linker");

        assert!(generated.is_none(), "no-fallback unexpectedly generated {generated:?}");
        assert!(
            !dir.path().join("_stubs_freestanding.c").exists(),
            "no-fallback must not create a freestanding weak-stub source artifact"
        );
        assert!(
            !dir.path().join("_stubs_freestanding.o").exists(),
            "no-fallback must not create a freestanding weak-stub object artifact"
        );
    }
    #[test]
    fn stale_module_move_is_detected_and_rt_channels_are_untouched() {
        // The live 2026-07-28 instance: `skip_wrap_spaces` moved from the
        // `_layout` module to `_foundation`; a stale cached caller object kept
        // the dead `_layout` reference while the real body sits in the same link.
        let dead = "lib__gc_async_mut__gpu__browser_engine__renderer_layout__skip_wrap_spaces";
        let live = "lib__gc_async_mut__gpu__browser_engine__renderer_foundation__skip_wrap_spaces";
        let defined: HashSet<String> = [live, "os__kernel__mm__map_page"]
            .iter()
            .map(|s| (*s).to_string())
            .collect();

        let report = stale_module_move_report(&[dead.to_string()], &defined)
            .expect("a dead module-prefixed reference with a live sibling must be reported");
        assert!(report.contains(dead), "report names the dead symbol");
        assert!(report.contains(live), "report names the module it moved to");
        assert!(report.contains("stale object cache"), "report names the cause");

        // No sibling under a different prefix -> not this class, stays quiet.
        assert!(stale_module_move_report(
            &["lib__common__text__genuinely_absent".to_string()],
            &defined
        )
        .is_none());

        // `rt_*` externs are a different channel and must not be disturbed.
        assert!(simple_module_symbol_tail("rt_array_copy").is_none());
        assert!(stale_module_move_report(&["rt_array_copy".to_string()], &defined).is_none());

        // A symbol undefined in one object and defined in another under the SAME
        // name is ordinary cross-object linkage, not a move.
        assert!(stale_module_move_report(&[live.to_string()], &defined).is_none());

        // Tail extraction takes everything after the LAST separator.
        assert_eq!(simple_module_symbol_tail(live), Some("skip_wrap_spaces"));
        assert_eq!(
            simple_module_symbol_tail("os__kernel__mm__map_page"),
            Some("map_page")
        );
    }

    #[test]
    fn compatibility_aliases_use_gc_boundaries_and_elf_discards_siblings() {
        assert_ne!(
            alias_gc_section(TargetOS::Linux, 0),
            alias_gc_section(TargetOS::Linux, 1)
        );
        assert!(alias_gc_section(TargetOS::Windows, 0).contains(".text$stub_0"));
        assert_eq!(alias_gc_prelude(TargetOS::MacOS), ".subsections_via_symbols\n");

        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        {
            use std::fs;
            use std::process::Command;

            let dir = tempfile::tempdir().unwrap();
            let aliases = dir.path().join("aliases.s");
            let main = dir.path().join("main.c");
            let binary = dir.path().join("probe");
            fs::write(
                &aliases,
                format!(
                    "{} .weak used_alias\nused_alias:\n  jmp used_target\n\n{} .weak unused_alias\nunused_alias:\n  jmp missing_sibling_target\n\n.section .note.GNU-stack,\"\",@progbits\n",
                    alias_gc_section(TargetOS::Linux, 0),
                    alias_gc_section(TargetOS::Linux, 1),
                ),
            )
            .unwrap();
            fs::write(
                &main,
                "extern long used_alias(void); long used_target(void) { return 7; } int main(void) { return used_alias() != 7; }\n",
            )
            .unwrap();

            let link = Command::new("cc")
                .arg("-ffunction-sections")
                .arg("-Wl,--gc-sections")
                .arg(&main)
                .arg(&aliases)
                .arg("-o")
                .arg(&binary)
                .output()
                .unwrap();
            assert!(link.status.success(), "{}", String::from_utf8_lossy(&link.stderr));
            assert!(Command::new(&binary).status().unwrap().success());
        }
    }

    #[test]
    fn runtime_owned_symbols_are_not_suffix_aliased() {
        let defined = HashSet::from(["m_01_unit__spec__rt_hashmap_new".to_string()]);

        assert_eq!(resolve_defined_suffix_alias("__rt_hashmap_new", &defined), None);
        assert_eq!(resolve_defined_suffix_alias("rt_thread_join", &defined), None);
    }

    #[test]
    fn non_runtime_symbols_can_still_suffix_alias() {
        let defined = HashSet::from(["m_01_unit__spec__helper".to_string()]);

        assert_eq!(
            resolve_defined_suffix_alias("helper", &defined),
            Some("m_01_unit__spec__helper".to_string())
        );
    }

    #[test]
    fn qualified_alias_prefers_unique_full_module_suffix() {
        let defined = HashSet::from([
            "nogc_sync_mut__io__env_ops__env_get".to_string(),
            "common__config__env_get".to_string(),
        ]);

        assert_eq!(
            resolve_defined_suffix_alias("io__env_ops__env_get", &defined),
            Some("nogc_sync_mut__io__env_ops__env_get".to_string())
        );
        assert_eq!(
            resolve_defined_suffix_alias("_io__env_ops__env_get", &defined),
            Some("nogc_sync_mut__io__env_ops__env_get".to_string())
        );
        assert_eq!(resolve_defined_suffix_alias("other__env_get", &defined), None);
    }

    #[test]
    fn ambiguous_short_alias_is_rejected() {
        let defined = HashSet::from([
            "tier_x86_64__app__cli__run_check".to_string(),
            "tier_scalar__tool__check__run_check".to_string(),
        ]);

        assert_eq!(resolve_defined_suffix_alias("run_check", &defined), None);
    }

    #[test]
    fn fabricated_stub_baseline_parses_rows_and_comments() {
        let rows = parse_fabricated_stub_baseline(
            "# header\n\nkernel.elf rt_array_copy  # debt\n kernel.elf rt_dma_alloc\nother.elf rt_x\n",
        )
        .unwrap();
        assert_eq!(rows.len(), 3);
        assert!(rows.contains(&("kernel.elf".to_string(), "rt_array_copy".to_string())));
        assert!(rows.contains(&("other.elf".to_string(), "rt_x".to_string())));
    }

    #[test]
    fn malformed_baseline_row_is_an_error_not_an_empty_baseline() {
        assert!(parse_fabricated_stub_baseline("kernel.elf\n").is_err());
        assert!(parse_fabricated_stub_baseline("a b c\n").is_err());
    }

    #[test]
    fn new_fabricated_symbols_are_partitioned_out() {
        let rows = parse_fabricated_stub_baseline("kernel.elf rt_known\n").unwrap();
        let (known, new_syms) = partition_fabricated_against_baseline(
            &rows,
            "kernel.elf",
            &["rt_known".to_string(), "rt_brand_new".to_string()],
        );
        assert_eq!(known, vec!["rt_known".to_string()]);
        assert_eq!(new_syms, vec!["rt_brand_new".to_string()]);
    }

    #[test]
    fn baseline_rows_are_scoped_per_entry() {
        let rows = parse_fabricated_stub_baseline("other.elf rt_known\n").unwrap();
        let (known, new_syms) =
            partition_fabricated_against_baseline(&rows, "kernel.elf", &["rt_known".to_string()]);
        assert!(known.is_empty());
        assert_eq!(new_syms, vec!["rt_known".to_string()]);
    }

    #[test]
    fn rewrite_replaces_only_the_target_entry_and_keeps_comments() {
        let existing = "# doc line\nkernel.elf rt_old\nother.elf rt_keep\n";
        let updated =
            rewrite_fabricated_stub_baseline(existing, "kernel.elf", &["rt_a".to_string(), "rt_b".to_string()]);
        assert!(updated.contains("# doc line"));
        assert!(updated.contains("other.elf rt_keep"));
        assert!(!updated.contains("kernel.elf rt_old"));
        assert!(updated.contains("kernel.elf rt_a"));
        assert!(updated.contains("kernel.elf rt_b"));
        // The rewrite output must round-trip through the parser.
        let rows = parse_fabricated_stub_baseline(&updated).unwrap();
        assert_eq!(rows.len(), 3);
    }

    #[test]
    fn entry_key_is_the_output_basename() {
        assert_eq!(
            fabricated_stub_entry_key(Path::new("/a/b/simple_wm_kernel.elf")),
            "simple_wm_kernel.elf"
        );
    }

    #[test]
    fn ratchet_fires_on_new_symbol_for_baselined_entry_and_passes_on_known() {
        // End-to-end fire-path probe of check_fabricated_stub_ratchet itself:
        // a baselined entry with a NEW fabricated symbol must be a hard Err,
        // and the identical build with only known symbols must pass. This is
        // the vacuity check for the gate -- the pure helpers are covered
        // above, but only this function decides pass/fail.
        let dir = std::env::temp_dir().join(format!(
            "fabricated_ratchet_fire_test_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let baseline = dir.join("baseline.sdn");
        std::fs::write(&baseline, "kernel.elf rt_known\n").unwrap();
        // Point the checker at the temp baseline. No other test reads these
        // env vars, so per-process mutation cannot race a parallel test.
        // Clear the write/strict knobs in case the ambient environment set
        // them -- either would change the pass/fail decision under test.
        std::env::remove_var("SIMPLE_FABRICATED_STUB_BASELINE_WRITE");
        std::env::remove_var("SIMPLE_STRICT_FABRICATED_STUB_RATCHET");
        std::env::set_var("SIMPLE_FABRICATED_STUB_BASELINE", &baseline);

        let known_only = ["rt_known".to_string()];
        let ok = check_fabricated_stub_ratchet(&dir, Path::new("kernel.elf"), &known_only);

        let with_new = ["rt_known".to_string(), "rt_probe_new_symbol".to_string()];
        let fired = check_fabricated_stub_ratchet(&dir, Path::new("kernel.elf"), &with_new);

        std::env::remove_var("SIMPLE_FABRICATED_STUB_BASELINE");
        let _ = std::fs::remove_dir_all(&dir);

        assert!(ok.is_ok(), "known-only fabricated set must pass: {ok:?}");
        let err = fired.expect_err("a NEW fabricated symbol on a baselined entry must fail the link");
        assert!(
            err.contains("rt_probe_new_symbol"),
            "ratchet error must name the new symbol: {err}"
        );
    }

    #[test]
    fn shipped_baseline_file_parses() {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|p| p.parent())
            .and_then(|p| p.parent())
            .map(std::path::Path::to_path_buf)
            .unwrap();
        let path = repo_root.join("config/freestanding_fabricated_stub_baseline.sdn");
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        parse_fabricated_stub_baseline(&text).unwrap();
        assert!(
            text.contains("SIMPLE_FABRICATED_STUB_BASELINE_WRITE"),
            "baseline file must document the regeneration procedure the code implements"
        );
    }
}
