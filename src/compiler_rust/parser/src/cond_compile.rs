//! Line-level conditional compilation: `@when(<cond>):` / `@elif(<cond>):` /
//! `@else:` / `@end`.
//!
//! Mirrors pass 1 of the pure-Simple preprocessor
//! (`src/compiler/10.frontend/core/parser_preprocessor.spl`): directive lines
//! and every line of an inactive branch are blanked (line numbers and byte
//! offsets are preserved), so the parser sees exactly one branch. Conditions
//! use the same grammar (`not`/`!`, `and`/`&&`, `or`/`||`, parentheses, bare
//! OS/arch atoms, `os=`/`platform=`/`arch=`/`target_arch=`/`cpu=` key-value
//! atoms with `=` or `==`). An unrecognised atom evaluates to `false` and is
//! reported as a diagnostic instead of a parse error.
//!
//! The target defaults to `SIMPLE_TARGET_OS` / `SIMPLE_TARGET_ARCH` (same env
//! override as `cfg_platform.spl`), falling back to the host. Native builds
//! for an explicit `--target` already strip these blocks against the build
//! target before parsing, so this pass then finds no directives.

/// Canonical OS name for a raw spelling, or `""` if unknown.
pub fn normalize_os(raw: &str) -> &'static str {
    match strip_quotes(raw) {
        "win" | "windows" | "Windows" | "Windows_NT" => "windows",
        "linux" | "Linux" => "linux",
        "mac" | "macos" | "MacOS" | "darwin" | "Darwin" => "macos",
        "freebsd" | "FreeBSD" => "freebsd",
        "openbsd" | "OpenBSD" => "openbsd",
        "netbsd" | "NetBSD" => "netbsd",
        "android" | "Android" => "android",
        "simpleos" | "SimpleOS" => "simpleos",
        "none" => "none",
        "unix" | "Unix" => "unix",
        _ => "",
    }
}

/// Canonical architecture name for a raw spelling, or `""` if unknown.
pub fn normalize_arch(raw: &str) -> &'static str {
    match strip_quotes(raw) {
        "x86_64" | "amd64" | "AMD64" | "x64" | "X64" => "x86_64",
        "x86" | "X86" | "i386" | "i686" => "x86",
        "aarch64" | "arm64" | "ARM64" => "aarch64",
        "arm" | "ARM" | "armv6" | "armv7" => "arm",
        "riscv64" => "riscv64",
        "riscv32" => "riscv32",
        "ppc64le" | "ppc64el" | "powerpc64le" => "ppc64le",
        "thumbv6m" => "thumbv6m",
        "thumbv7m" => "thumbv7m",
        "thumbv7em" => "thumbv7em",
        _ => "",
    }
}

/// The (os, arch) conditions are evaluated against by default.
pub fn default_target() -> (&'static str, &'static str) {
    let env_os = std::env::var("SIMPLE_TARGET_OS").map(|v| normalize_os(&v)).unwrap_or("");
    let env_arch = std::env::var("SIMPLE_TARGET_ARCH")
        .map(|v| normalize_arch(&v))
        .unwrap_or("");
    let os = if !env_os.is_empty() {
        env_os
    } else {
        match normalize_os(std::env::consts::OS) {
            "" => "unknown",
            os => os,
        }
    };
    let arch = if !env_arch.is_empty() {
        env_arch
    } else {
        match normalize_arch(std::env::consts::ARCH) {
            "" => "unknown",
            arch => arch,
        }
    };
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
            "unix" => matches!(
                self.os,
                "linux" | "macos" | "freebsd" | "openbsd" | "netbsd" | "android" | "simpleos"
            ),
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

    fn atom(&mut self, token: &str) -> bool {
        let t = strip_quotes(token);
        match t {
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
                "os" | "platform" => return self.os_match(value),
                "arch" | "target_arch" | "cpu" => return self.arch_match(value),
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
    /// Columns to remove from a kept line's indentation so a branch body that
    /// is indented under its `@when` lexes at the directive's own level.
    pub dedent: Vec<usize>,
    /// Unsupported atoms / unbalanced directives (never parse errors).
    pub diagnostics: Vec<String>,
}

fn indent_width(line: &str) -> usize {
    let mut width = 0;
    for ch in line.chars() {
        match ch {
            ' ' => width += 1,
            '\t' => width += 4,
            _ => break,
        }
    }
    width
}

struct Frame {
    parent: bool,
    taken: bool,
    directive_indent: usize,
    body_indent: Option<usize>,
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
    let mut dedent = Vec::new();
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
                directive_indent: indent_width(line),
                body_indent: None,
            });
            active = current;
        } else if t.starts_with("@elif(") {
            if let Some(frame) = stack.last_mut() {
                let mut current = false;
                if frame.parent && !frame.taken {
                    current = eval(paren_condition(t), &mut diagnostics);
                    frame.taken |= current;
                }
                frame.body_indent = None;
                active = current;
            } else {
                diagnostics.push(format!("line {line_no}: @elif without @when (ignored)"));
            }
        } else if t == "@else" || t == "@else:" {
            if let Some(frame) = stack.last_mut() {
                let current = frame.parent && !frame.taken;
                frame.taken |= current;
                frame.body_indent = None;
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
            let mut offset = 0;
            if let (Some(outer), Some(inner)) = (stack.first().map(|f| f.directive_indent), stack.last_mut()) {
                if inner.body_indent.is_none() && !t.is_empty() && !t.starts_with('#') {
                    inner.body_indent = Some(indent_width(line));
                }
                offset = inner.body_indent.unwrap_or(outer).saturating_sub(outer);
            }
            skip.push(!active);
            dedent.push(offset);
            any |= !active || offset > 0;
            continue;
        }
        skip.push(true);
        dedent.push(0);
        any = true;
    }
    if !stack.is_empty() {
        diagnostics.push("unclosed @when block".to_string());
    }
    if any || !diagnostics.is_empty() {
        Some(LineMask {
            skip,
            dedent,
            diagnostics,
        })
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "@when(os=\"windows\"):\n    fn a() -> i64: 1\n@else:\n    fn a() -> i64: 2\n@end\n";

    fn kept(source: &str, os: &str, arch: &str) -> Vec<String> {
        let mask = inactive_line_mask(source, os, arch).expect("directives present").skip;
        source
            .split('\n')
            .zip(mask)
            .filter(|(l, m)| !m && !l.trim().is_empty())
            .map(|(l, _)| l.trim().to_string())
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
        assert!(!eval_condition("os = \"windows\"", "linux", "x86_64").0);
    }

    #[test]
    fn unsupported_atom_is_false_with_diagnostic() {
        let (value, diags) = eval_condition("feature=\"gpu\"", "linux", "x86_64");
        assert!(!value);
        assert_eq!(diags.len(), 1);
        let src = "@when(feature=\"gpu\"):\nG\n@else:\nE\n@end\n";
        assert_eq!(kept(src, "linux", "x86_64"), vec!["E"]);
    }

    #[test]
    fn indented_branch_body_is_dedented_to_directive_level() {
        let src = "@when(windows):\n    fn a():\n        pass\n@else:\n  fn a():\n      pass\n@end\n";
        let m = inactive_line_mask(src, "windows", "x86_64").unwrap();
        assert_eq!(m.dedent[1..3], [4, 4]);
        let m = inactive_line_mask(src, "linux", "x86_64").unwrap();
        assert_eq!(m.dedent[4..6], [2, 2]);
    }

    #[test]
    fn no_directives_is_none() {
        assert!(inactive_line_mask("fn main():\n    pass\n", "linux", "x86_64").is_none());
    }
}
