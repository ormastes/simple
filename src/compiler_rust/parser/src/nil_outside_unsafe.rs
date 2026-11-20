//! NIL-UNSAFE-001: `nil` is allowed only inside `unsafe`.
//!
//! Rust twin of `src/compiler/90.tools/lint/rules/nil_outside_unsafe_rule.spl`
//! (same scanner, same codes and wording). Safe code spells absence `None`.
//! Presence tests (`x == nil`, `x != nil`, `case nil`) are flagged too. The
//! unit-type `Nil` value (`return nil` / tail `nil` in a `-> Nil` fn, `Ok(nil)`
//! in `-> Result<Nil, E>`) is exempt. Scope is the `unsafe:` / `danger:` block
//! only; an `@unsafe` fn attribute does not exempt.
//!
//! Off by default, like pure-Simple's `allow` level; `SIMPLE_LINT_NIL_UNSAFE=1`
//! turns the reporting on.

/// One finding: 1-based line and column plus the shared message text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NilFinding {
    pub line: usize,
    pub col: usize,
    pub message: &'static str,
    pub hint: &'static str,
}

const MSG_NIL: &str = "`nil` outside `unsafe`: safe code spells absence `None`";
const HINT_NIL: &str = "use `None` (Option); keep `nil` only inside an `unsafe:` block";
const MSG_CMP: &str = "comparison with `nil` outside `unsafe`: test Option presence instead";
const HINT_CMP: &str = "`x == nil` -> `x.is_none()`, `x != nil` -> `x.is_some()`, `case nil` -> `case None`, or `if val v = x` (None != nil natively; migrate the callee's `return nil` to `return None` in the same change)";

impl NilFinding {
    /// Diagnostic line shared by every reporter.
    pub fn render(&self) -> String {
        format!(
            "warning[NIL-UNSAFE-001]: {} (line {}:{}); {}",
            self.message, self.line, self.col, self.hint
        )
    }
}

/// Whether the reporting is switched on (`SIMPLE_LINT_NIL_UNSAFE=1`).
pub fn nil_lint_enabled() -> bool {
    matches!(std::env::var("SIMPLE_LINT_NIL_UNSAFE").as_deref(), Ok("1") | Ok("true") | Ok("warn"))
}

/// Report every finding for `path` on stderr when the lint is enabled.
/// Shared by the module loader and the native-project compiler.
pub fn report_nil_outside_unsafe(path: &std::path::Path, source: Option<&str>) {
    if !nil_lint_enabled() {
        return;
    }
    let owned;
    let text = match source {
        Some(s) => s,
        None => match std::fs::read_to_string(path) {
            Ok(s) => {
                owned = s;
                &owned
            }
            Err(_) => return,
        },
    };
    for f in find_nil_outside_unsafe(text) {
        eprintln!("{}: {}", path.display(), f.render());
    }
}

fn is_word(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn indent_of(line: &str) -> usize {
    line.bytes().take_while(|b| *b == b' ' || *b == b'\t').count()
}

fn triple_count(line: &str) -> usize {
    let b = line.as_bytes();
    let (mut n, mut i) = (0, 0);
    while i + 3 <= b.len() {
        if &b[i..i + 3] == b"\"\"\"" {
            n += 1;
            i += 3;
        } else {
            i += 1;
        }
    }
    n
}

fn blank_triple_spans(line: &str) -> String {
    let b = line.as_bytes();
    let mut out = String::new();
    let (mut inside, mut i) = (false, 0);
    while i < b.len() {
        if i + 3 <= b.len() && &b[i..i + 3] == b"\"\"\"" {
            inside = !inside;
            out.push_str("   ");
            i += 3;
            continue;
        }
        out.push(if inside || b[i] >= 0x80 { ' ' } else { b[i] as char });
        i += 1;
    }
    out
}

/// Blank string bodies and drop a trailing comment, keeping byte columns.
fn code_of(line: &str) -> String {
    let b = line.as_bytes();
    let mut out = String::new();
    let mut quote: u8 = 0;
    let mut i = 0;
    while i < b.len() {
        let ch = b[i];
        let shown = if ch >= 0x80 { ' ' } else { ch as char };
        if quote != 0 {
            if ch == b'\\' {
                out.push_str("  ");
                i += 2;
                continue;
            }
            if ch == quote {
                quote = 0;
                out.push(shown);
            } else {
                out.push(' ');
            }
        } else if ch == b'"' || ch == b'\'' {
            quote = ch;
            out.push(shown);
        } else if ch == b'#' {
            return out;
        } else {
            out.push(shown);
        }
        i += 1;
    }
    out
}

fn ends_with_keyword(trimmed: &str, kw: &str) -> bool {
    if !trimmed.ends_with(kw) {
        return false;
    }
    let at = trimmed.len() - kw.len();
    at == 0 || !is_word(trimmed.as_bytes()[at - 1])
}

fn opens_unsafe_block(code: &str) -> bool {
    let t = code.trim();
    if ends_with_keyword(t, "unsafe:") || ends_with_keyword(t, "danger:") {
        return true;
    }
    t.ends_with("):")
        && (t.starts_with("unsafe(") || t.starts_with("danger(") || t.contains(" unsafe(") || t.contains(" danger("))
}

fn keyword_at(code: &str, kw: &str) -> Option<usize> {
    let mut start = 0;
    while start < code.len() {
        let at = start + code[start..].find(kw)?;
        if at == 0 || !is_word(code.as_bytes()[at - 1]) {
            return Some(at);
        }
        start = at + kw.len();
    }
    None
}

fn inline_unsafe_column(code: &str) -> Option<usize> {
    match (keyword_at(code, "unsafe:"), keyword_at(code, "danger:")) {
        (Some(u), Some(d)) => Some(u.min(d)),
        (u, d) => u.or(d),
    }
}

fn is_presence_test(code: &str, at: usize) -> bool {
    let before = code[..at].trim();
    let after = code[at + 3..].trim();
    before.ends_with("==")
        || before.ends_with("!=")
        || after.starts_with("==")
        || after.starts_with("!=")
        || before.ends_with("case")
        || before.ends_with('|')
}

fn nil_columns(code: &str) -> Vec<usize> {
    let b = code.as_bytes();
    let mut cols = Vec::new();
    let mut start = 0;
    while start + 3 <= code.len() {
        let Some(rel) = code[start..].find("nil") else { break };
        let at = start + rel;
        let before_ok = at == 0 || (!is_word(b[at - 1]) && b[at - 1] != b'.');
        let after_ok = at + 3 >= code.len() || !is_word(b[at + 3]);
        if before_ok && after_ok {
            cols.push(at);
        }
        start = at + 3;
    }
    cols
}

/// -1 not a fn header, 0 other return, 1 `-> Nil` / `-> ()`, 2 `Result<Nil|(), E>`.
fn unit_return_kind(code: &str) -> i32 {
    let mut t = code.trim();
    for p in ["pub ", "export ", "static ", "async "] {
        if let Some(rest) = t.strip_prefix(p) {
            t = rest.trim();
        }
    }
    if !(t.starts_with("fn ") || t.starts_with("me ")) || !t.ends_with(':') {
        return -1;
    }
    let Some(arrow) = t.rfind("->") else { return 0 };
    let ret = t[arrow + 2..t.len() - 1].replace(' ', "");
    if ret == "Nil" || ret == "()" {
        return 1;
    }
    if ret.starts_with("Result<Nil,") || ret.starts_with("Result<(),") {
        return 2;
    }
    0
}

fn is_unit_value(code: &str, at: usize, kind: i32) -> bool {
    let before = code[..at].trim();
    let after = code[at + 3..].trim();
    match kind {
        1 => after.is_empty() && (before.is_empty() || before == "return"),
        2 => before.ends_with("Ok(") && after.starts_with(')'),
        _ => false,
    }
}

/// Scan source text; returns every `nil` outside an `unsafe` block.
pub fn find_nil_outside_unsafe(content: &str) -> Vec<NilFinding> {
    let mut out = Vec::new();
    let mut in_doc = false;
    let mut unsafe_indent: i64 = -1;
    let mut unit_fn_indent: i64 = -1;
    let mut unit_fn_kind = 0;
    for (idx, line) in content.split('\n').enumerate() {
        let line_num = idx + 1;
        let line = line.strip_suffix('\r').unwrap_or(line);
        let has_quote = line.contains('"');
        if !in_doc && (line.contains("Nil") || line.contains("()") || unit_fn_indent >= 0) {
            let fn_code = code_of(line);
            if !fn_code.trim().is_empty() {
                let fi = indent_of(&fn_code) as i64;
                if unit_fn_indent >= 0 && fi <= unit_fn_indent {
                    unit_fn_indent = -1;
                    unit_fn_kind = 0;
                }
                let hk = unit_return_kind(&fn_code);
                if hk > 0 || (hk == 0 && unit_fn_indent >= 0) {
                    unit_fn_indent = fi;
                    unit_fn_kind = hk;
                }
            }
        }
        if !in_doc && !has_quote && !line.contains("nil") && !line.contains("unsafe") && !line.contains("danger") {
            let rt = line.trim();
            if unsafe_indent >= 0 && !rt.is_empty() && !rt.starts_with('#') && indent_of(line) as i64 <= unsafe_indent {
                unsafe_indent = -1;
            }
            continue;
        }
        let quotes = if has_quote { triple_count(line) } else { 0 };
        if in_doc {
            if quotes % 2 == 1 {
                in_doc = false;
            }
            continue;
        }
        if quotes % 2 == 1 {
            in_doc = true;
            continue;
        }
        let unquoted = if quotes > 0 { blank_triple_spans(line) } else { line.to_string() };
        let code = code_of(&unquoted);
        if code.trim().is_empty() {
            continue;
        }
        let indent = indent_of(&code) as i64;
        if unsafe_indent >= 0 && indent <= unsafe_indent {
            unsafe_indent = -1;
        }
        if unsafe_indent < 0 && opens_unsafe_block(&code) {
            unsafe_indent = indent;
            continue;
        }
        if unsafe_indent >= 0 || !code.contains("nil") {
            continue;
        }
        let inline = inline_unsafe_column(&code);
        for col in nil_columns(&code) {
            if inline.is_some_and(|u| col > u) {
                continue;
            }
            if unit_fn_kind > 0 && is_unit_value(&code, col, unit_fn_kind) {
                continue;
            }
            let cmp = is_presence_test(&code, col);
            out.push(NilFinding {
                line: line_num,
                col: col + 1,
                message: if cmp { MSG_CMP } else { MSG_NIL },
                hint: if cmp { HINT_CMP } else { HINT_NIL },
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flags_plain_nil() {
        let f = find_nil_outside_unsafe("fn f():\n    val x = nil\n");
        assert_eq!(f.len(), 1);
        assert_eq!((f[0].line, f[0].col), (2, 13));
        assert!(f[0].render().contains("NIL-UNSAFE-001") && f[0].render().contains("use `None`"));
    }

    #[test]
    fn flags_presence_tests() {
        let src = "fn f(x):\n    if x == nil:\n        pass\n    if x != nil:\n        pass\n    match x:\n        case nil:\n            pass\n";
        let f = find_nil_outside_unsafe(src);
        assert_eq!(f.len(), 3);
        assert!(f.iter().all(|x| x.message == MSG_CMP));
    }

    #[test]
    fn unsafe_block_and_inline_are_exempt() {
        let src = "fn f():\n    unsafe:\n        val x = nil\n    val y = 1\n    val z = unsafe: nil\n    danger:\n        return nil\n";
        assert!(find_nil_outside_unsafe(src).is_empty());
    }

    #[test]
    fn nil_after_unsafe_block_is_flagged() {
        let src = "fn f():\n    unsafe:\n        val x = nil\n    val y = nil\n";
        let f = find_nil_outside_unsafe(src);
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].line, 4);
    }

    #[test]
    fn unit_nil_and_ok_nil_exempt() {
        let src = "fn a() -> Nil:\n    return nil\nfn b() -> Result<Nil, text>:\n    Ok(nil)\nfn c() -> i64?:\n    return nil\n";
        let f = find_nil_outside_unsafe(src);
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].line, 6);
    }

    #[test]
    fn comments_strings_and_names_ignored() {
        let src = "fn f():\n    val a = \"nil\"  # nil\n    val b = nilable\n    val c = x.nil\n    val d = \"\"\"\n    nil\n    \"\"\"\n";
        assert!(find_nil_outside_unsafe(src).is_empty());
    }

    #[test]
    fn unsafe_attribute_fn_not_exempt() {
        let f = find_nil_outside_unsafe("@unsafe\nfn f():\n    return nil\n");
        assert_eq!(f.len(), 1);
    }
}
