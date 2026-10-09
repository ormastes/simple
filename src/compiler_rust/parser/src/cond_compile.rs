//! Line-level conditional compilation: `@when(<cond>):` / `@elif(<cond>):` /
//! `@else:` / `@end`.
//!
//! This is the seed half of ONE grammar shared with the pure-Simple
//! preprocessor (`src/compiler/10.frontend/core/parser_preprocessor.spl`,
//! pass 1). Both are pinned to the same corpus,
//! `test/fixtures/conditional_compile/conformance/` (see `expectations.tsv`,
//! `env_targets.tsv`, `owner_files.txt`), by
//! `parser/tests/when_block_conformance.rs` here and
//! `test/01_unit/compiler/frontend/when_block_conformance_spec.spl` there.
//!
//! Grammar (identical on both sides):
//!   * A directive is alone on its line (leading whitespace allowed). Directive
//!     lines and every line of an inactive branch are blanked; kept lines are
//!     emitted VERBATIM -- branch bodies are flat (written at the directive's
//!     own indentation), never dedented. Line numbers are preserved.
//!   * Conditions: `or`/`||`, `and`/`&&`, `not`/`!`, parentheses, atoms.
//!   * Atom values may be quoted (`"` or `'`) and are case-insensitive; a
//!     key/value atom uses `=` or `==`, with any spacing (`os="x"`, `os = "x"`,
//!     `os ="x"`, `os= "x"` are all one atom: `=`/`==` are tokens of their own).
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
//!   * Structure: `@elif`/`@else`/`@end` without an open `@when`, or an
//!     unclosed `@when`, leave the mask `balanced == false`. Every consumer
//!     fails closed on that (the parser returns a syntax error, the text
//!     strip path returns `Err`): both branches are never compiled.
//!
//! Target selection: `SIMPLE_TARGET_OS` / `SIMPLE_TARGET_ARCH`, else the
//! `SIMPLE_NATIVE_BUILD_TARGET` triple, else the host -- the same order as
//! `cfg_platform.spl` (`cfg_detect_os` / `cfg_detect_arch`). An explicit
//! target (`Lexer::new_for_target`) overrides all of them. Environment and
//! host spellings are normalised with the FUZZY rule shared with
//! `cfg_normalize_os` / `cfg_normalize_arch` ([`normalize_host_os`],
//! [`normalize_host_arch`]: lowercase, substring match in a fixed order, so
//! `Windows_NT`, `darwin23`, `linux-gnu`, `AMD64`, `x86_64-pc-linux-gnu` all
//! resolve); atom VALUES use the exact alias table above.

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

/// Canonical OS for an environment / host spelling (`Windows_NT`,
/// `darwin23.1`, `linux-gnu`, `uname -s` output...). Mirrors
/// `cfg_platform.spl` `cfg_normalize_os` exactly: lowercase, then the first
/// matching substring in this order.
pub fn normalize_host_os(raw: &str) -> &'static str {
    let v = strip_quotes(raw).to_ascii_lowercase();
    if v.is_empty() {
        return "";
    }
    if v == "win" || v.contains("windows") {
        return "windows";
    }
    if v.contains("linux") {
        return "linux";
    }
    if v == "mac" || v.contains("macos") || v.contains("darwin") || v.contains("mac") {
        return "macos";
    }
    if v.contains("freebsd") {
        return "freebsd";
    }
    if v.contains("openbsd") {
        return "openbsd";
    }
    if v.contains("simpleos") {
        return "simpleos";
    }
    if v.contains("netbsd") {
        return "netbsd";
    }
    if v.contains("android") {
        return "android";
    }
    if v.contains("unix") {
        return "unix";
    }
    if v == "none" || v == "baremetal" {
        return "none";
    }
    ""
}

/// Canonical arch for an environment / host spelling (`AMD64`,
/// `x86_64-pc-linux-gnu`, `riscv64gc`, `uname -m` output...). Mirrors
/// `cfg_platform.spl` `cfg_normalize_arch` exactly.
pub fn normalize_host_arch(raw: &str) -> &'static str {
    let v = strip_quotes(raw).to_ascii_lowercase();
    if v.is_empty() {
        return "";
    }
    if v == "x64" || v.contains("x86_64") || v.contains("amd64") {
        return "x86_64";
    }
    if v == "x86" || v.contains("i386") || v.contains("i686") {
        return "x86";
    }
    if v.contains("aarch64") || v.contains("arm64") {
        return "aarch64";
    }
    if v.starts_with("thumbv6m") {
        return "thumbv6m";
    }
    if v.starts_with("thumbv7em") {
        return "thumbv7em";
    }
    if v.starts_with("thumbv7m") {
        return "thumbv7m";
    }
    if v == "arm" || v == "arm32" || v.contains("armv7") || v.contains("armv6") {
        return "arm";
    }
    if v.contains("riscv64") {
        return "riscv64";
    }
    if v.contains("riscv32") {
        return "riscv32";
    }
    if v == "ppc64el" || v.contains("ppc64le") || v.contains("powerpc64le") {
        return "ppc64le";
    }
    ""
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
        let os = if lower == "win32" { "windows" } else { normalize_host_os(&lower) };
        if !os.is_empty() && os != "unix" {
            return os;
        }
    }
    ""
}

/// cfg arch of a target triple (`riscv64gc-unknown-linux-gnu` -> `riscv64`);
/// a single component is not a triple. Mirrors `cfg_platform.spl`
/// `cfg_triple_arch`.
pub fn triple_arch(triple: &str) -> &'static str {
    let parts: Vec<&str> = triple.trim().split('-').collect();
    if parts.len() < 2 {
        return "";
    }
    normalize_host_arch(parts[0])
}

fn env_value(key: &str) -> String {
    std::env::var(key).unwrap_or_default()
}

/// The (os, arch) conditions are evaluated against when no explicit target is
/// given: `SIMPLE_TARGET_OS`/`SIMPLE_TARGET_ARCH` > `SIMPLE_NATIVE_BUILD_TARGET`
/// triple > host.
pub fn default_target() -> (&'static str, &'static str) {
    let triple = env_value("SIMPLE_NATIVE_BUILD_TARGET");
    let mut os = normalize_host_os(&env_value("SIMPLE_TARGET_OS"));
    if os.is_empty() {
        os = triple_os(&triple);
    }
    if os.is_empty() {
        os = match normalize_host_os(std::env::consts::OS) {
            "" => "unknown",
            host => host,
        };
    }
    let mut arch = normalize_host_arch(&env_value("SIMPLE_TARGET_ARCH"));
    if arch.is_empty() {
        arch = triple_arch(&triple);
    }
    if arch.is_empty() {
        arch = match normalize_host_arch(std::env::consts::ARCH) {
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
        // `=` / `==` are tokens of their own: re-join `key`, operator, value
        // into one atom whatever the spacing was.
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
            '&' | '|' | '=' if chars.get(i + 1) == Some(&ch) => {
                flush(&mut current, &mut tokens);
                tokens.push(format!("{ch}{ch}"));
                i += 1;
            }
            '=' => {
                flush(&mut current, &mut tokens);
                tokens.push("=".to_string());
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
    /// `false` when a directive had no open `@when` or a `@when` was never
    /// closed. Consumers must fail closed on this (see module docs).
    pub balanced: bool,
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
    let mut balanced = true;
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
                balanced = false;
                diagnostics.push(format!("line {line_no}: @elif without @when"));
            }
        } else if t == "@else" || t == "@else:" {
            if let Some(frame) = stack.last_mut() {
                let current = frame.parent && !frame.taken;
                frame.taken |= current;
                active = current;
            } else {
                balanced = false;
                diagnostics.push(format!("line {line_no}: @else without @when"));
            }
        } else if t == "@end" {
            match stack.pop() {
                Some(frame) => active = frame.parent,
                None => {
                    balanced = false;
                    diagnostics.push(format!("line {line_no}: @end without @when"));
                }
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
        balanced = false;
        diagnostics.push("unclosed @when block".to_string());
    }
    if any || !diagnostics.is_empty() {
        Some(LineMask {
            skip,
            balanced,
            diagnostics,
        })
    } else {
        None
    }
}

/// Text-level result of [`select_branches`].
#[derive(Debug, Clone)]
pub struct Selection {
    /// Source with directive and inactive lines blanked (same line count).
    pub source: String,
    /// `false` on unbalanced directives; consumers fail closed.
    pub balanced: bool,
    /// Diagnostics (unsupported atoms, structural problems).
    pub diagnostics: Vec<String>,
}

/// Apply conditional compilation as text: directive lines and inactive-branch
/// lines become empty, kept lines are copied verbatim, so the result has the
/// same line count as `source`. This is byte-for-byte what the pure-Simple
/// preprocessor's first pass produces. Returns `source` unchanged (balanced,
/// no diagnostics) when it contains no directive.
pub fn select_branches(source: &str, os: &str, arch: &str) -> Selection {
    let Some(mask) = inactive_line_mask(source, os, arch) else {
        return Selection {
            source: source.to_owned(),
            balanced: true,
            diagnostics: Vec::new(),
        };
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
    Selection {
        source: out,
        balanced: mask.balanced,
        diagnostics: mask.diagnostics,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "@when(os=\"windows\"):\nfn a() -> i64: 1\n@else:\nfn a() -> i64: 2\n@end\n";

    fn kept(source: &str, os: &str, arch: &str) -> Vec<String> {
        select_branches(source, os, arch)
            .source
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
    fn operators_aliases_and_spacing() {
        assert!(eval_condition("!(win || darwin) && arm64", "linux", "aarch64").0);
        assert!(eval_condition("not os='mac'", "linux", "x86_64").0);
        assert!(eval_condition("target_arch == amd64", "linux", "x86_64").0);
        assert!(eval_condition("target_os = Linux and cpu = X64", "linux", "x86_64").0);
        assert!(eval_condition("family=\"unix\" and not family=windows", "freebsd", "x86_64").0);
        assert!(eval_condition("platform='Darwin' or baremetal", "none", "riscv64").0);
        assert!(!eval_condition("os = \"windows\"", "linux", "x86_64").0);
        for spaced in ["os =\"linux\"", "os= \"linux\"", "os  ==  \"linux\"", "os==\"linux\""] {
            let (value, diags) = eval_condition(spaced, "linux", "x86_64");
            assert!(value && diags.is_empty(), "{spaced}: {diags:?}");
        }
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
        let sel = select_branches(src, "linux", "x86_64");
        assert!(sel.balanced && sel.diagnostics.is_empty());
        assert_eq!(sel.source, "fn f():\n\n\n\n    val x = 2\n\n    x\n");
        assert_eq!(sel.source.split('\n').count(), src.split('\n').count());
    }

    #[test]
    fn unbalanced_directives_are_flagged() {
        for src in ["@else:\nX\n", "@end\n", "@elif(linux):\n", "@when(linux):\nX\n"] {
            let sel = select_branches(src, "linux", "x86_64");
            assert!(!sel.balanced, "{src:?}");
            assert!(!sel.diagnostics.is_empty(), "{src:?}");
        }
        assert!(select_branches(SRC, "linux", "x86_64").balanced);
    }

    #[test]
    fn host_spellings_use_the_shared_fuzzy_rule() {
        assert_eq!(normalize_host_os("Windows_NT"), "windows");
        assert_eq!(normalize_host_os("darwin23.1"), "macos");
        assert_eq!(normalize_host_os("linux-gnu"), "linux");
        assert_eq!(normalize_host_os("none"), "none");
        assert_eq!(normalize_host_os("FreeBSD"), "freebsd");
        assert_eq!(normalize_host_arch("AMD64"), "x86_64");
        assert_eq!(normalize_host_arch("x86_64-pc-linux-gnu"), "x86_64");
        assert_eq!(normalize_host_arch("riscv64gc"), "riscv64");
        assert_eq!(normalize_host_arch("arm64"), "aarch64");
        assert_eq!(normalize_host_arch("Intel64 Family 6"), "");
        // Atom values stay exact: a host spelling is not an atom.
        assert_eq!(normalize_os("Windows_NT"), "");
        assert_eq!(normalize_arch("x86_64-pc-linux-gnu"), "");
    }

    #[test]
    fn triple_selection_matches_cfg_platform() {
        assert_eq!((triple_os("x86_64-pc-windows-msvc"), triple_arch("x86_64-pc-windows-msvc")), ("windows", "x86_64"));
        assert_eq!((triple_os("aarch64-apple-darwin"), triple_arch("aarch64-apple-darwin")), ("macos", "aarch64"));
        assert_eq!((triple_os("riscv64gc-unknown-none-elf"), triple_arch("riscv64gc-unknown-none-elf")), ("none", "riscv64"));
        assert_eq!((triple_os("x86_64-unknown-simpleos"), triple_arch("x86_64-unknown-simpleos")), ("simpleos", "x86_64"));
        assert_eq!((triple_os("thumbv7em-none-eabihf"), triple_arch("thumbv7em-none-eabihf")), ("none", "thumbv7em"));
        assert_eq!((triple_os("garbage"), triple_arch("x86_64")), ("", ""));
    }

    #[test]
    fn no_directives_is_none() {
        assert!(inactive_line_mask("fn main():\n    pass\n", "linux", "x86_64").is_none());
        let sel = select_branches("fn main():\n    pass\n", "linux", "x86_64");
        assert_eq!(sel.source, "fn main():\n    pass\n");
        assert!(sel.balanced && sel.diagnostics.is_empty());
    }
}
