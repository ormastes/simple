//! Line-level conditional compilation: `@when(<cond>):` / `@elif(<cond>):` /
//! `@else:` / `@end`.
//!
//! This is the seed half of ONE grammar shared with the pure-Simple
//! preprocessor (`src/compiler/10.frontend/core/parser_preprocessor.spl`,
//! pass 1). Both are pinned to the same corpus,
//! `test/fixtures/conditional_compile/conformance/` (see `expectations.tsv`),
//! by `parser/tests/when_block_conformance.rs` here and
//! `test/01_unit/compiler/frontend/when_block_conformance_spec.spl` there.
//!
//! Grammar (identical on both sides):
//!   * A directive is alone on its line (leading whitespace allowed). Directive
//!     lines and every line of an inactive branch are blanked; kept lines are
//!     emitted VERBATIM -- branch bodies are flat (written at the directive's
//!     own indentation), never dedented. Line numbers are preserved.
//!   * Conditions: `or`/`||`, `and`/`&&`, `not`/`!`, parentheses, atoms.
//!   * Atom values may be quoted (`"` or `'`) and are case-insensitive; a
//!     key/value atom uses `=` or `==`, spaces allowed.
//!   * Atoms: `true` `compiled` `debug` (true); `false` `interpreter`
//!     `release` (false); a bare OS or arch name; `os=`/`platform=`/
//!     `target_os=` (OS); `arch=`/`target_arch=`/`cpu=` (arch);
//!     `family=`/`target_family=` (`unix` | `windows`); `feature=<name>`
//!     (always false: no features are defined). Anything else evaluates to
//!     `false` and is reported as a diagnostic, never a parse error.
//!   * OS names: windows (win), linux, macos (mac, darwin), freebsd, openbsd,
//!     netbsd, android, simpleos, none (baremetal), unix (= the family).
//!   * Arch names: x86_64 (amd64, x64), x86 (i386, i686), aarch64 (arm64),
//!     arm (arm32, armv6, armv7), riscv64, riscv32, ppc64le (ppc64el,
//!     powerpc64le), thumbv6m, thumbv7m, thumbv7em.
//!
//! Target selection: `SIMPLE_TARGET_OS` / `SIMPLE_TARGET_ARCH`, else the
//! `SIMPLE_NATIVE_BUILD_TARGET` triple, else the host -- the same order as
//! `cfg_platform.spl` (`cfg_detect_os` / `cfg_detect_arch`). An explicit
//! target (`Lexer::new_for_target`) overrides all of them.

/// Canonical OS name for an atom value, or `""` if unknown.
pub fn normalize_os(raw: &str) -> &'static str {
    match strip_quotes(raw).to_ascii_lowercase().as_str() {
        "windows" | "win" => "windows",
        "linux" => "linux",
        "macos" | "mac" | "darwin" => "macos",
        "freebsd" => "freebsd",
        "openbsd" => "openbsd",
        "netbsd" => "netbsd",
        "android" => "android",
        "simpleos" => "simpleos",
        "none" | "baremetal" => "none",
        "unix" => "unix",
        _ => "",
    }
}

/// Canonical architecture name for an atom value, or `""` if unknown.
pub fn normalize_arch(raw: &str) -> &'static str {
    match strip_quotes(raw).to_ascii_lowercase().as_str() {
        "x86_64" | "amd64" | "x64" => "x86_64",
        "x86" | "i386" | "i686" => "x86",
        "aarch64" | "arm64" => "aarch64",
        "arm" | "arm32" | "armv6" | "armv7" => "arm",
        "riscv64" => "riscv64",
        "riscv32" => "riscv32",
        "ppc64le" | "ppc64el" | "powerpc64le" => "ppc64le",
        "thumbv6m" => "thumbv6m",
        "thumbv7m" => "thumbv7m",
        "thumbv7em" => "thumbv7em",
        _ => "",
    }
}

/// OS set selected by the `unix` predicate / `family=unix`.
pub fn is_unix(os: &str) -> bool {
    matches!(
        os,
        "linux" | "macos" | "freebsd" | "openbsd" | "netbsd" | "android" | "simpleos" | "unix"
    )
}

/// cfg OS of a target triple (`x86_64-pc-windows-msvc` -> `windows`,
/// `aarch64-unknown-none` -> `none`), `""` when no component names one.
/// Mirrors `cfg_platform.spl` `cfg_triple_os`.
pub fn triple_os(triple: &str) -> &'static str {
    for part in triple.trim().split('-').skip(1) {
        let lower = part.to_ascii_lowercase();
        if lower == "none" || lower == "baremetal" {
            return "none";
        }
        let os = if lower == "win32" { "windows" } else { normalize_os(&lower) };
        if !os.is_empty() && os != "unix" {
            return os;
        }
    }
    ""
}

/// cfg arch of a target triple (`riscv64gc-unknown-linux-gnu` -> `riscv64`).
/// Mirrors `cfg_platform.spl` `cfg_triple_arch`.
pub fn triple_arch(triple: &str) -> &'static str {
    let first = triple.trim().split('-').next().unwrap_or("").to_ascii_lowercase();
    let exact = normalize_arch(&first);
    if !exact.is_empty() {
        return exact;
    }
    const PREFIXES: [(&str, &str); 10] = [
        ("riscv64", "riscv64"),
        ("riscv32", "riscv32"),
        ("thumbv7em", "thumbv7em"),
        ("thumbv7m", "thumbv7m"),
        ("thumbv6m", "thumbv6m"),
        ("aarch64", "aarch64"),
        ("x86_64", "x86_64"),
        ("powerpc64le", "ppc64le"),
        ("armv7", "arm"),
        ("armv6", "arm"),
    ];
    PREFIXES
        .iter()
        .find(|(prefix, _)| first.starts_with(prefix))
        .map(|(_, arch)| *arch)
        .unwrap_or("")
}

fn env_value(key: &str) -> String {
    std::env::var(key).unwrap_or_default()
}

/// The (os, arch) conditions are evaluated against when no explicit target is
/// given: `SIMPLE_TARGET_OS`/`SIMPLE_TARGET_ARCH` > `SIMPLE_NATIVE_BUILD_TARGET`
/// triple > host.
pub fn default_target() -> (&'static str, &'static str) {
    let triple = env_value("SIMPLE_NATIVE_BUILD_TARGET");
    let mut os = normalize_os(&env_value("SIMPLE_TARGET_OS"));
    if os.is_empty() {
        os = triple_os(&triple);
    }
    if os.is_empty() {
        os = match normalize_os(std::env::consts::OS) {
            "" => "unknown",
            host => host,
        };
    }
    let mut arch = normalize_arch(&env_value("SIMPLE_TARGET_ARCH"));
    if arch.is_empty() {
        arch = triple_arch(&triple);
    }
    if arch.is_empty() {
        arch = match normalize_arch(std::env::consts::ARCH) {
            "" => "unknown",
            host => host,
        };
    }
    (os, arch)
}

fn strip_quotes(value: &str) -> &str {
    let t = value.trim();
    if t.len() >= 2 && ((t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\''))) {
        &t[1..t.len() - 1]
    } else {
        t
    }
}

struct CondEval<'s> {
    tokens: Vec<String>,
    pos: usize,
    os: &'s str,
    arch: &'s str,
    diagnostics: Vec<String>,
}

impl CondEval<'_> {
    fn os_match(&mut self, raw: &str) -> bool {
        match normalize_os(raw) {
            "unix" => is_unix(self.os),
            "" => {
                self.diagnostics.push(format!("unsupported cfg OS `{raw}` (treated as false)"));
                false
            }
            os => self.os == os,
        }
    }

    fn arch_match(&mut self, raw: &str) -> bool {
        match normalize_arch(raw) {
            "" => {
                self.diagnostics
                    .push(format!("unsupported cfg architecture `{raw}` (treated as false)"));
                false
            }
            arch => self.arch == arch,
        }
    }

    fn family_match(&mut self, raw: &str) -> bool {
        match strip_quotes(raw).to_ascii_lowercase().as_str() {
            "unix" => is_unix(self.os),
            "windows" => self.os == "windows",
            _ => {
                self.diagnostics.push(format!("unsupported cfg family `{raw}` (treated as false)"));
                false
            }
        }
    }

    fn atom(&mut self, token: &str) -> bool {
        let t = strip_quotes(token);
        match t.to_ascii_lowercase().as_str() {
            "true" | "compiled" | "debug" => return true,
            "false" | "interpreter" | "release" => return false,
            _ => {}
        }
        if !normalize_os(t).is_empty() {
            return self.os_match(t);
        }
        if !normalize_arch(t).is_empty() {
            return self.arch_match(t);
        }
        let split = if t.contains("==") { t.split_once("==") } else { t.split_once('=') };
        if let Some((key, value)) = split {
            let value = strip_quotes(value);
            match strip_quotes(key) {
                "os" | "platform" | "target_os" => return self.os_match(value),
                "arch" | "target_arch" | "cpu" => return self.arch_match(value),
                "family" | "target_family" => return self.family_match(value),
                "feature" => return false,
                _ => {}
            }
        }
        self.diagnostics
            .push(format!("unsupported cfg condition atom `{t}` (treated as false)"));
        false
    }

    fn peek(&self) -> &str {
        self.tokens.get(self.pos).map(String::as_str).unwrap_or("")
    }

    fn take(&mut self) -> String {
        let tok = self.peek().to_string();
        if !tok.is_empty() {
            self.pos += 1;
        }
        tok
    }

    fn parse_or(&mut self) -> bool {
        let mut left = self.parse_and();
        while matches!(self.peek(), "or" | "||") {
            self.take();
            let right = self.parse_and();
            left = left || right;
        }
        left
    }

    fn parse_and(&mut self) -> bool {
        let mut left = self.parse_not();
        while matches!(self.peek(), "and" | "&&") {
            self.take();
            let right = self.parse_not();
            left = left && right;
        }
        left
    }

    fn parse_not(&mut self) -> bool {
        if matches!(self.peek(), "not" | "!") {
            self.take();
            return !self.parse_not();
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> bool {
        if self.peek() == "(" {
            self.take();
            let value = self.parse_or();
            if self.peek() == ")" {
                self.take();
            }
            return value;
        }
        let atom = self.take();
        // Re-join a spaced `key = value` / `key == value` atom.
        let mut eq = String::new();
        while matches!(self.peek(), "=" | "==") {
            eq.push_str(&self.take());
        }
        if !eq.is_empty() {
            let value = self.take();
            return self.atom(&format!("{atom}{eq}{value}"));
        }
        self.atom(&atom)
    }
}

fn tokenize_condition(condition: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let chars: Vec<char> = condition.chars().collect();
    let mut i = 0;
    let flush = |current: &mut String, tokens: &mut Vec<String>| {
        if !current.is_empty() {
            tokens.push(std::mem::take(current));
        }
    };
    while i < chars.len() {
        let ch = chars[i];
        match ch {
            ' ' | '\t' | '\r' => flush(&mut current, &mut tokens),
            '(' | ')' | '!' => {
                flush(&mut current, &mut tokens);
                tokens.push(ch.to_string());
            }
            '&' | '|' if chars.get(i + 1) == Some(&ch) => {
                flush(&mut current, &mut tokens);
                tokens.push(format!("{ch}{ch}"));
                i += 1;
            }
            _ => current.push(ch),
        }
        i += 1;
    }
    flush(&mut current, &mut tokens);
    tokens
}

/// Evaluate a condition against `(os, arch)`. Diagnostics name every atom
/// that was not understood (and therefore evaluated to `false`).
pub fn eval_condition(condition: &str, os: &str, arch: &str) -> (bool, Vec<String>) {
    let mut ev = CondEval {
        tokens: tokenize_condition(condition),
        pos: 0,
        os,
        arch,
        diagnostics: Vec::new(),
    };
    if ev.tokens.is_empty() {
        return (false, vec!["empty cfg condition (treated as false)".to_string()]);
    }
    let value = ev.parse_or();
    if ev.pos != ev.tokens.len() {
        ev.diagnostics
            .push(format!("malformed cfg condition `{condition}` (trailing tokens ignored)"));
    }
    (value, ev.diagnostics)
}

/// Text between the first `(` and its matching `)`.
fn paren_condition(line: &str) -> &str {
    let Some(start) = line.find('(') else { return "" };
    let mut depth = 1;
    for (i, ch) in line[start + 1..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return line[start + 1..start + 1 + i].trim();
                }
            }
            _ => {}
        }
    }
    line[start + 1..].trim()
}

/// Result of the conditional-compilation pass, indexed by 0-based line.
#[derive(Debug, Clone)]
pub struct LineMask {
    /// `true` for directive lines and lines of inactive branches.
    pub skip: Vec<bool>,
    /// Unsupported atoms / unbalanced directives (never parse errors).
    pub diagnostics: Vec<String>,
}

struct Frame {
    parent: bool,
    taken: bool,
}

/// Compute the [`LineMask`] for `source`. `None` when the source contains no
/// directive at all (the common case).
pub fn inactive_line_mask(source: &str, os: &str, arch: &str) -> Option<LineMask> {
    if !(source.contains("@when(") || source.contains("@elif(") || source.contains("@else") || source.contains("@end"))
    {
        return None;
    }
    let mut stack: Vec<Frame> = Vec::new();
    let mut active = true;
    let mut skip = Vec::new();
    let mut diagnostics = Vec::new();
    let mut any = false;
    for (index, line) in source.split('\n').enumerate() {
        let t = line.trim();
        let line_no = index + 1;
        let mut eval = |cond: &str, diagnostics: &mut Vec<String>| {
            let (value, diags) = eval_condition(cond, os, arch);
            diagnostics.extend(diags.into_iter().map(|d| format!("line {line_no}: {d}")));
            value
        };
        if t.starts_with("@when(") {
            let cond_ok = eval(paren_condition(t), &mut diagnostics);
            let current = active && cond_ok;
            stack.push(Frame {
                parent: active,
                taken: current,
            });
            active = current;
        } else if t.starts_with("@elif(") {
            if let Some(frame) = stack.last_mut() {
                let mut current = false;
                if frame.parent && !frame.taken {
                    current = eval(paren_condition(t), &mut diagnostics);
                    frame.taken |= current;
                }
                active = current;
            } else {
                diagnostics.push(format!("line {line_no}: @elif without @when (ignored)"));
            }
        } else if t == "@else" || t == "@else:" {
            if let Some(frame) = stack.last_mut() {
                let current = frame.parent && !frame.taken;
                frame.taken |= current;
                active = current;
            } else {
                diagnostics.push(format!("line {line_no}: @else without @when (ignored)"));
            }
        } else if t == "@end" {
            match stack.pop() {
                Some(frame) => active = frame.parent,
                None => diagnostics.push(format!("line {line_no}: @end without @when (ignored)")),
            }
        } else {
            skip.push(!active);
            any |= !active;
            continue;
        }
        skip.push(true);
        any = true;
    }
    if !stack.is_empty() {
        diagnostics.push("unclosed @when block".to_string());
    }
    if any || !diagnostics.is_empty() {
        Some(LineMask { skip, diagnostics })
    } else {
        None
    }
}

/// Apply conditional compilation as text: directive lines and inactive-branch
/// lines become empty, kept lines are copied verbatim, so the result has the
/// same line count as `source`. This is byte-for-byte what the pure-Simple
/// preprocessor's first pass produces. Returns `source` unchanged (and no
/// diagnostics) when it contains no directive.
pub fn select_branches(source: &str, os: &str, arch: &str) -> (String, Vec<String>) {
    let Some(mask) = inactive_line_mask(source, os, arch) else {
        return (source.to_owned(), Vec::new());
    };
    let mut out = String::with_capacity(source.len());
    for (index, line) in source.split('\n').enumerate() {
        if index > 0 {
            out.push('\n');
        }
        if !mask.skip.get(index).copied().unwrap_or(false) {
            out.push_str(line);
        }
    }
    (out, mask.diagnostics)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "@when(os=\"windows\"):\nfn a() -> i64: 1\n@else:\nfn a() -> i64: 2\n@end\n";

    fn kept(source: &str, os: &str, arch: &str) -> Vec<String> {
        let (selected, _) = select_branches(source, os, arch);
        selected
            .split('\n')
            .filter(|l| !l.trim().is_empty())
            .map(|l| l.trim().to_string())
            .collect()
    }

    #[test]
    fn windows_branch_active() {
        assert_eq!(kept(SRC, "windows", "x86_64"), vec!["fn a() -> i64: 1"]);
    }

    #[test]
    fn else_branch_active_for_non_windows_targets() {
        for os in ["linux", "macos", "freebsd", "simpleos"] {
            for arch in ["x86_64", "aarch64", "riscv64"] {
                assert_eq!(kept(SRC, os, arch), vec!["fn a() -> i64: 2"], "{os}/{arch}");
            }
        }
    }

    #[test]
    fn elif_chain_and_nesting() {
        let src = "@when(os=\"windows\"):\nW\n@elif(os == \"linux\" and arch=\"aarch64\"):\nLA\n@when(riscv64):\nNEVER\n@end\n@elif(unix):\nU\n@else:\nE\n@end\n";
        assert_eq!(kept(src, "windows", "x86_64"), vec!["W"]);
        assert_eq!(kept(src, "linux", "aarch64"), vec!["LA"]);
        assert_eq!(kept(src, "linux", "x86_64"), vec!["U"]);
        assert_eq!(kept(src, "simpleos", "riscv64"), vec!["U"]);
        assert_eq!(kept(src, "none", "thumbv7em"), vec!["E"]);
    }

    #[test]
    fn operators_and_aliases() {
        assert!(eval_condition("!(win || darwin) && arm64", "linux", "aarch64").0);
        assert!(eval_condition("not os='mac'", "linux", "x86_64").0);
        assert!(eval_condition("target_arch == amd64", "linux", "x86_64").0);
        assert!(eval_condition("target_os = Linux and cpu = X64", "linux", "x86_64").0);
        assert!(eval_condition("family=\"unix\" and not family=windows", "freebsd", "x86_64").0);
        assert!(eval_condition("platform='Darwin' or baremetal", "none", "riscv64").0);
        assert!(!eval_condition("os = \"windows\"", "linux", "x86_64").0);
        let (value, diags) = eval_condition("feature=\"gpu\"", "linux", "x86_64");
        assert!(!value && diags.is_empty(), "feature= is a recognised key that is always false");
    }

    #[test]
    fn unsupported_atom_is_false_with_diagnostic() {
        let (value, diags) = eval_condition("vendor=\"acme\"", "linux", "x86_64");
        assert!(!value);
        assert_eq!(diags.len(), 1);
        let src = "@when(vendor=\"acme\"):\nG\n@else:\nE\n@end\n";
        assert_eq!(kept(src, "linux", "x86_64"), vec!["E"]);
    }

    #[test]
    fn kept_lines_are_verbatim_and_line_count_is_preserved() {
        let src = "fn f():\n    @when(windows):\n    val x = 1\n    @else:\n    val x = 2\n    @end\n    x\n";
        let (selected, diags) = select_branches(src, "linux", "x86_64");
        assert!(diags.is_empty());
        assert_eq!(selected, "fn f():\n\n\n\n    val x = 2\n\n    x\n");
        assert_eq!(selected.split('\n').count(), src.split('\n').count());
    }

    #[test]
    fn triple_selection_matches_cfg_platform() {
        assert_eq!((triple_os("x86_64-pc-windows-msvc"), triple_arch("x86_64-pc-windows-msvc")), ("windows", "x86_64"));
        assert_eq!((triple_os("aarch64-apple-darwin"), triple_arch("aarch64-apple-darwin")), ("macos", "aarch64"));
        assert_eq!((triple_os("riscv64gc-unknown-none-elf"), triple_arch("riscv64gc-unknown-none-elf")), ("none", "riscv64"));
        assert_eq!((triple_os("x86_64-unknown-simpleos"), triple_arch("x86_64-unknown-simpleos")), ("simpleos", "x86_64"));
        assert_eq!((triple_os("thumbv7em-none-eabihf"), triple_arch("thumbv7em-none-eabihf")), ("none", "thumbv7em"));
        assert_eq!(triple_os("garbage"), "");
    }

    #[test]
    fn no_directives_is_none() {
        assert!(inactive_line_mask("fn main():\n    pass\n", "linux", "x86_64").is_none());
        let (same, diags) = select_branches("fn main():\n    pass\n", "linux", "x86_64");
        assert_eq!(same, "fn main():\n    pass\n");
        assert!(diags.is_empty());
    }
}
