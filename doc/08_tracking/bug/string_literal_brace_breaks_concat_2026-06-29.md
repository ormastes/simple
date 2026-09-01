# Bug: unescaped `{` in a string literal corrupts `+` concatenation in the same expression

- **ID:** string_literal_brace_breaks_concat_2026-06-29
- **Severity:** P2 (silently emits the source `" + var + "` verbatim → invalid CSS/JSON, blank web render)
- **Area:** language / interpreter (string-literal interpolation lexing)
- **Status:** open — minimal repro confirmed; app-level workaround landed in `src/os/compositor/simple_web_window_renderer.spl`

## Summary
When a string literal containing an **unescaped single `{`** is part of a `+`
concatenation expression, the interpolation scanner does not stop at the literal's
closing `"`. It swallows the `" + var + "` operators (and everything up to the next
`}`) as interpolation/literal text, so the concatenated variables are never
substituted — the raw source `" + var + "` appears verbatim in the output.

## Minimal repro (confirmed on `release/x86_64-unknown-linux-gnu/simple`, interpreter path)
```simple
var x = "VAL"
print "a " + x + " b"        # => "a VAL b"           (OK, no brace)
print "p { " + x + " }"      # => "p  + x + "          (WRONG)
print "p { q: " + x + "; }"  # => "p { q: " + x + "; }" (WRONG — verbatim)
```

## Real-world impact
`_simple_web_window_css` built its theme CSS with `":root { --glass-accent: " + accent + "; ... }"`.
Every `+ color +` was emitted verbatim, so the rendered CSS carried no real colors →
all-white frame. This broke `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl`
("exposes SimpleOS app pixels through the common web render artifact": `_count_changed == 0`).

## Workaround (used in the fix)
Build such strings with interpolation `{var}` plus **escaped** literal braces
`\{` / `\}` (both confirmed to round-trip to a single literal brace, no stray backslash):
```simple
":root \{ --glass-accent: {accent}; \} ..."
```

## Expected behavior
The interpolation scanner must terminate at the string literal's closing `"`; a `{`
with no matching `}` inside the same literal should be a literal brace (or a lex error),
never consume following concatenation operators.

## Related
- [[string_literal_double_brace_collapse_2026-06-16]] — sibling brace-in-literal defect (`{{`/`}}` collapse).
- [[angle_bracket_index_lint_parse_mismatch_2026-06-06]] — separate JIT generics-vs-index
  false positive (`rules[pos] < x`) that forces compositor specs onto the interpreter path
  where this bug surfaces.
