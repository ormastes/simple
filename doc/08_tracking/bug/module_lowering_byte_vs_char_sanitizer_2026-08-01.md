# module_lowering byte-vs-char path sanitizer miscounts on non-ASCII module paths

- **Id:** module_lowering_byte_vs_char_sanitizer_2026-08-01
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** P3 — impact is non-ASCII module/file paths only (≈never in practice)
- **Found:** 2026-08-01 (divergence parallel scan, Wave 11)
- **Component:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`

## Symptom

The module-path sanitizer loop (around line 176) bounds on `mod_path.len()`
(a **BYTE** count) but reads `mod_path.char_code_at(_san_i)` / `char_at(_san_i)`
(**CHAR**-indexed). On a multibyte path it runs more iterations than there are
characters, appending a spurious trailing `_`. Oracle: `"fé_bar"` sanitizes to
`"f__bar_"` instead of the intended `"f__bar"`.

This is the same byte-vs-char family swept across `src/**` on 2026-08-01, but it
is **deliberately not fixed yet**.

## Why deferred (do not "just convert to .chars()")

The function carries a hand-tuned native-codegen workaround (see the comment at
lines 169–174): `for ch in <text>` yields a corrupted loop element in the seed
interpreter AND in pure-Simple-compiled native code, which is exactly why the
code uses explicit `char_code_at` indexing. A naive `val cs = mod_path.chars()`
conversion risks re-triggering that same native corruption, and it **cannot be
verified without a native build** (the seed oracle only proves interp behavior).
See `doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`.

## Resume plan

- Verify `.chars()` decodes correctly under **native** codegen (needs a build),
  OR find a byte-consistent fix that keeps `char_code_at` but bounds on the
  character count without `for ch in text`.
- Confirm the sanitized name change does not alter stage4 module-collision
  behavior (the loop's stated purpose).
- Owner: unassigned. Blocked-on: a native build to verify `.chars()`.
