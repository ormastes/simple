//! Native CSS rule-boundary scanner for the interpreter.
//!
//! `simple_web_html_layout_renderer.spl`'s `extract_css_vw` parses the
//! browser's theme stylesheet (a few hundred KB, ~1800 rules) by walking the
//! CSS text one character at a time in interpreted Simple code, tracking
//! brace depth to find rule/selector/declaration boundaries. Under the
//! tree-walking interpreter that single-character loop costs on the order of
//! a few hundred microseconds PER CHARACTER (confirmed by direct
//! measurement: ~292,000 characters took ~86 seconds in `count_css_rules`
//! alone, before `extract_css_vw`'s own near-identical second pass), so the
//! whole render hangs for minutes on realistic theme CSS.
//!
//! This function performs the exact same brace-depth bookkeeping natively in
//! Rust (microseconds instead of minutes) and hands back the already-sliced
//! selector/declaration text for each candidate rule — NOT offsets. This
//! matters because the interpreter's own `text.substring(start, end)`
//! builtin (`interpreter_method/string.rs`) re-collects the ENTIRE receiver
//! string into a `Vec<char>` on every call regardless of the requested
//! window (confirmed by measurement); handing back ~1800 pairs of offsets
//! and letting Simple call `.substring()` on the original ~292KB CSS text
//! for each one reintroduces an O(rules * total_css_len) cost on top of the
//! scan this function was written to eliminate. Slicing natively here (a
//! single already-collected `Vec<char>`, genuine O(window) per rule) avoids
//! that trap entirely. All other CSS semantics — selector-group splitting,
//! `@media` condition evaluation, CSS-variable substitution, declaration
//! parsing — stay in Simple, unchanged.
//!
//! Depth-0 non-`@` blocks are ordinary rules. Depth-0 `@`-blocks are wrappers
//! (`@media`, `@supports`, `@layer`, ...) whose depth-1 children are
//! candidate rules; for those, `wrapper_prelude` carries the wrapper's raw
//! prelude text (e.g. `"@media (max-width: 600px)"`) so the Simple caller can
//! apply its existing `_media_prelude_applies` filter unchanged. Rules with
//! an empty `wrapper_prelude` are always included (top-level rules, and
//! children of any non-`@media` wrapper, matching the prior behavior where
//! `cur_at_active` defaults to `true` for non-media at-rules).

use crate::error::CompileError;
use crate::value::Value;

#[inline]
fn is_ascii_ws(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

/// First index in `chars[start..end)` that is not ASCII whitespace, or `None`.
fn first_non_ws(chars: &[char], start: usize, end: usize) -> Option<usize> {
    (start..end).find(|&i| !is_ascii_ws(chars[i]))
}

/// Trim ASCII whitespace off both ends of `chars[start..end)` and collect to
/// a `String` — the native equivalent of `css.substring(start, end).trim()`,
/// but O(window) instead of O(len(css)) per call.
fn sliced_trim(chars: &[char], start: usize, end: usize) -> String {
    let mut a = start;
    let mut b = end;
    while a < b && is_ascii_ws(chars[a]) {
        a += 1;
    }
    while b > a && is_ascii_ws(chars[b - 1]) {
        b -= 1;
    }
    chars[a..b].iter().collect()
}

/// `rt_css_scan_rule_bounds(css: text) -> [[text], [text], [text]]`
///
/// Returns three parallel arrays (all same length, one entry per candidate
/// rule, in document order): `sel_text` (trimmed selector text), `decl_text`
/// (trimmed declaration body text), and `wrapper_prelude` (text, `""` when
/// the rule is unconditional).
pub fn scan_rule_bounds(args: &[Value]) -> Result<Value, CompileError> {
    let css = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let chars: Vec<char> = css.chars().collect();
    let n = chars.len();

    let mut sel_text: Vec<Value> = Vec::new();
    let mut decl_text: Vec<Value> = Vec::new();
    let mut wrapper_prelude: Vec<Value> = Vec::new();

    let mut depth: i32 = 0;
    let mut sel0: usize = 0;
    let mut sel1: usize = 0;
    let mut cur_at = false;
    let mut wrapper_prelude_cur = String::new();

    let mut p0_sel: usize = 0;
    let mut p0_brace: usize = 0;
    let mut p0_emit = false;
    let mut p1_sel: usize = 0;
    let mut p1_brace: usize = 0;
    let mut p1_emit = false;

    let mut i = 0usize;
    while i < n {
        let c = chars[i];
        if c == '{' {
            if depth == 0 {
                let ss = first_non_ws(&chars, sel0, i);
                cur_at = matches!(ss, Some(p) if chars[p] == '@');
                p0_sel = sel0;
                p0_brace = i;
                p0_emit = ss.is_some() && !cur_at;
                wrapper_prelude_cur = if cur_at {
                    let start = ss.unwrap();
                    chars[start..i].iter().collect::<String>().trim().to_string()
                } else {
                    String::new()
                };
                depth = 1;
                sel1 = i + 1;
            } else if depth == 1 {
                if cur_at {
                    let ss1 = first_non_ws(&chars, sel1, i);
                    p1_sel = sel1;
                    p1_brace = i;
                    p1_emit = ss1.is_some();
                }
                depth = 2;
            } else {
                depth += 1;
            }
        } else if c == '}' {
            if depth == 1 {
                if p0_emit {
                    sel_text.push(Value::Str(sliced_trim(&chars, p0_sel, p0_brace)));
                    decl_text.push(Value::Str(sliced_trim(&chars, p0_brace + 1, i)));
                    wrapper_prelude.push(Value::Str(String::new()));
                }
                p0_emit = false;
                depth = 0;
                sel0 = i + 1;
            } else if depth == 2 {
                if cur_at && p1_emit {
                    sel_text.push(Value::Str(sliced_trim(&chars, p1_sel, p1_brace)));
                    decl_text.push(Value::Str(sliced_trim(&chars, p1_brace + 1, i)));
                    wrapper_prelude.push(Value::Str(wrapper_prelude_cur.clone()));
                }
                p1_emit = false;
                depth = 1;
                sel1 = i + 1;
            } else if depth > 0 {
                depth -= 1;
            }
        }
        i += 1;
    }

    Ok(Value::array(vec![
        Value::array(sel_text),
        Value::array(decl_text),
        Value::array(wrapper_prelude),
    ]))
}
