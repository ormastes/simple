# String interpolation brace scanner breaks across concatenated string literals

## Closed 2026-09-13 — fixed, re-verified by running the entry repro

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Ran the exact repro from the "Repro" section:

```spl
fn main():
    var css = "body{font:14px;"
    css = css + "color:#1a1f26;}"
    print(css)
    print("END")
```

Output:

```
body{font:14px;color:#1a1f26;}
END
```

The runtime value is exactly the concatenation of the two literals. No
adjacent source text leaks in, so the P1 silent source-text leak across
concatenated literals no longer reproduces (measured). The brace-depth
scanner no longer carries state across literal boundaries.

Note: a related but distinct brace inconsistency WITHIN a single literal is
still live and is tracked by
`interp_brace_literal_collides_with_string_interpolation_2026-07-03.md` and
`string_interpolation_css_brace_footgun_2026-07-03.md`.

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed) — CLOSED 2026-09-13 (see top section)

- **Date:** 2026-07-03
- **Severity:** P1 (wrong runtime string content — silent source-text leak)
- **Found by:** dashboard HTML/CSS generation in examples/12_business/simple_erp/src/web/dashboard.spl

## Repro

When a string literal opens a `{` brace whose matching `}` lands in a
*different* concatenated literal, the interpolation scanner mis-tracks the
brace depth and leaks raw source text (including the following line's code)
into the runtime string:

```
var css = "body{font:14px;"
css = css + "color:#1a1f26;}"
# runtime value of css contains literal source text from the next line
```

## Expected

`{` inside a string literal either starts an interpolation that must close in
the SAME literal, or (if unmatched) should be a parse error — never silent
leakage of adjacent source lines into the string value.

## Workaround

Keep `{`/`}` balanced within each single literal (e.g. one CSS rule per
literal). Applied in dashboard.spl.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
