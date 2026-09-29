# Bug: `text.index_of` returns `nil` for a present substring (Option<i64> mangled)

- **Filed:** 2026-07-07
- **Severity:** P1 (silent data loss in any Option<i64>-returning stdlib call)
- **Component:** self-hosted interpreter — string/Option value boxing
- **Status:** open; worked around in `src/app/llm_caret/json_helpers.spl`

## Symptom

`text.index_of(needle)` and `text.to_int()` both return `Option<i64>`, and both
mangle their result under the self-hosted binary (`bin/simple run`):

```
"abc:def".index_of(":")    # expected Some(3), OBSERVED nil
"abc:def".index_of("abc")  # index 0  -> 0        (correct)
"abc:def".index_of("zzz")  # absent   -> -1-ish   (matches nil branch oddly)
"7".to_int()  ?? -1        # OBSERVED <value:0x7>  (boxed, unrenderable)
"42".to_int() ?? -1        # OBSERVED 0.000...     (float-mangled handle)
```

The value that comes back through the `Option<i64>` channel is not a usable
`i64`: a present match at index 3 reports `nil`; `to_int` yields a boxed handle
rather than the integer.

## Root cause

Two related boxing defects, both in the small-int value channel:

1. **`Option<i64>` boxing** — `index_of` / `to_int` return `Option<i64>` whose
   payload is mangled (present match at index 3 → `nil`; `to_int` → heap
   handle). Consistent with the documented seed **int-boxing / tag-box wall**
   (memory `project_stage4_wall_and_hardening`). Mechanism not isolated to the
   bit level; recorded as hypothesis.

2. **`char.to_i64()` boxed across module boundaries** — CONFIRMED this session.
   `s[i].to_i64()` on a digit char returns the code point (e.g. `'7'`→55)
   correctly when the calling function is in the SAME module, but returns a
   boxed / digit-value form (`<value:0x7>` under JIT, `7` under the interpreter)
   when the function is called CROSS-MODULE. A hand digit loop written as
   `n*10 + (ch.to_i64() - 48)` therefore parses correctly same-module and
   mis-parses cross-module (interpreter: `"50"`→-478; JIT: `"50"`→0). Verified
   by a standalone probe: identical source, same-module correct / cross-module
   wrong. This is a JIT/interpreter cross-module miscompilation of
   `char.to_i64()`, not a source-logic defect.

## Impact

Every shipped `llm_caret` module parsed API responses with
`_unwrap_idx(json.index_of(...))` and `int(raw)`. Depending on where a key
lands in the response string, extracted values (including assistant message
text and usage token counts) could be silently dropped or corrupted.

## Workaround (applied)

`src/app/llm_caret/json_helpers.spl` now exposes two boxing-free primitives and
all shipped modules delegate to them:

- `json_find(s, needle) -> i64` — hand-written substring scan, bare `i64`; never
  routes an index through `Option<i64>`.
- `json_parse_int(s) -> i64` — digit loop using `_digit_val(ch)`, which maps a
  digit char to `0..9` by explicit `==` comparison (NO `char.to_i64()`). This is
  correct BOTH same-module and cross-module, under JIT and interpreter. Verified:
  cross-module `json_parse_int("50")` → 50, claude_api_spec 18/18, openai_api_spec
  16/16, claude_cli_spec 39/39, server_spec 22/22 (all previously red).

## Residual (out of scope — deeper compiler bug)

`extract_json_int` (composite: `json_find` + `substring` + `trim` +
`json_parse_int`) still returns a garbage handle when called CROSS-MODULE under
**JIT** (`bin/simple run`), while correct under the interpreter (the test runner
and current production path). `extract_json_string` — the assistant-text path —
is correct cross-module under JIT. So the residual only affects usage/token-count
integers when a caller is JIT-compiled cross-module. Root cause is the same
cross-module boxing class in the string-op chain (`substring`/`trim`), not
llm_caret logic. Tracked here; fix belongs in the compiler, not this app.

## Fix (upstream, TODO)

Root-cause and repair the interpreter's `Option<i64>` boxing so `index_of` /
`to_int` are usable directly. Until then, prefer bare-`i64` scans over the
Option-returning stdlib forms in hot parsing paths.
