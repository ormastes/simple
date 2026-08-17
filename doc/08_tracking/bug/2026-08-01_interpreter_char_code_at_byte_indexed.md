# Pure-Simple interpreter `text.char_code_at` was BYTE-indexed (cross-lane divergence)

- **Date:** 2026-08-01
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** High — the canonical default lane was the wrong one
- **Area:** `src/compiler/10.frontend/core/interpreter/`

## Summary

`text.char_code_at(i)` is CHARACTER (codepoint) indexed in every lane except the
pure-Simple interpreter, which indexed it by BYTE and then re-decoded a single
byte as UTF-8. On any string containing a multi-byte codepoint it returned
garbage at the multi-byte character and every index after it was shifted.

Measured on the pure-Simple interpreter, `"café,"` (6 bytes / 5 chars):

| expression | before | after | other lanes |
|---|---|---|---|
| `char_code_at(0)` | 99 | 99 | 99 |
| `char_code_at(3)` (`é`) | **65533** | 233 | 233 |
| `char_code_at(4)` (`,`) | **65533** | 44 | 44 |
| `char_code_at(5)` | 0 | 0 | 0 |
| `"日本".char_code_at(0)` | garbage | 26085 | 26085 |
| `"日本".char_code_at(1)` | garbage | 26412 | 26412 |

65533 is U+FFFD — the signature of `String::from_utf8_lossy` being handed the
bare `0xC3` lead byte of `é`. Note index 4 was *also* wrong: the byte index had
desynced from the character index, so the defect was not confined to the
non-ASCII character itself.

## Reference lanes (all three agree, all three are character-indexed)

- Seed: `src/compiler_rust/compiler/src/interpreter_method/string.rs` — `s.chars().nth(idx)`, with an all-ASCII / ASCII-prefix fast path.
- C runtime: `src/runtime/runtime_native.c` `rt_string_char_code_at` — explicit UTF-8 width walk (2/3/4-byte forms), returns 0 for negative and out-of-range.
- Pure-Simple runtime: `src/runtime/simple_core/core_string.spl` `rt_string_char_code_at` — same walk, same contract.

## Root cause

Two different byte-addressed spellings of the same mistake:

- `eval_methods.spl` — `val ch = s[idx:idx + 1]` then `ch.char_code_at(0)`
- `_EvalOps/access_literal_assign_eval.spl` — `val ch = s.substring(idx, idx + 1)` then `ch.char_code_at(0)`

Both `[a:b]` and `substring` are byte-indexed (deliberately — they must agree
with the byte offsets `len` and `index_of` hand out). Slicing one byte out of
the middle of a codepoint and decoding it as UTF-8 yields U+FFFD, not the raw
byte and not the codepoint.

Fix: delegate to the host builtin `s.char_code_at(idx)`, which lowers to
`__simple_rt_string_char_code_at` — the same shared runtime walk the compiled
lanes use. Bounds are handled inside the runtime (0 for negative and
out-of-range, matching the seed's `None => 0`), so the old `idx < s.len()` guard
was removed: `len` is BYTE length and therefore an over-estimate of the
character count, so only the walk knows the real end.

## THE IMPORTANT PART: `eval_text_method` is defined TWICE

`fn eval_text_method` exists in **both** files above. Fixing `eval_methods.spl`
alone changed **nothing observable** — a probe against the real evaluator still
returned 65533. The `_EvalOps/access_literal_assign_eval.spl` copy is the one
actually reached at runtime.

Only a behavioural probe caught this. A source-only review would have called the
first fix complete and shipped a still-broken interpreter.

The two copies are not equal: the `_EvalOps` copy is a strict **subset**. It has
arms for `len`, `contains`, `char_code_at`, `substring`, `starts_with`,
`ends_with`, `replace`, `split`, `split_lines`/`lines`, `trim`/`strip`,
`index_of` — and **no `byte_at`, no `char_at`, no `slice`, no `last_index_of`,
no `parse_int`, no `to_upper`/`to_lower`/`to_string`**. Those fall through to
`no method '<name>' on text` in the engine that actually runs.

Consequence: `test/01_unit/compiler/interpreter/text_byte_at_dispatch_spec.spl`
structurally guards `byte_at` in `eval_methods.spl` — the copy that does **not**
run. A probe confirmed `byte_at` returns 0 for every index through the live
evaluator. **Filed as follow-up, not fixed here** (out of scope): either
de-duplicate `eval_text_method` or port the missing arms into the live copy.

## Why a green suite would never have caught this

Four independent reasons, any one of which is sufficient:

1. **`simple test` silently delegates to the Rust seed child.** A spec asserting
   `"café,".char_code_at(3) == 233` passes before *and* after the fix, because
   the seed's implementation was always correct. The spec never touches the
   pure-Simple arm.
2. **`use std.spec` demotes a program to the interpreter**, so in-process specs
   cannot reach the JIT/codegen lanes either.
3. **The interpreter package has zero external importers.** Nothing outside
   `src/compiler/10.frontend/core/interpreter/` imports it, so no spec can load
   it by ordinary means. Every existing spec in
   `test/01_unit/compiler/interpreter/` is a *structural* source-text assertion
   for exactly this reason.
4. **`bin/simple` currently has no `test`/`run`/`lint`/`check` subcommands** at
   all, so the canonical tool cannot even be pointed at the code.

The defect was only ever observable from inside a built compiler — which is
where it silently corrupted every non-ASCII `char_code_at` call in the
interpreter lane.

## Verification

**Engine under test: the pure-Simple interpreter**
(`src/compiler/10.frontend/core/interpreter/`), driven through its own
`core_interpret_expr(source)` entry point. **Host: the Rust seed binary**
(`bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`), which
compiled and executed the interpreter *from current working-copy source* — so
the arm under test is the edited one, not a stale build.

The seed being the host does not weaken the evidence: the values under test are
produced by the pure-Simple `eval_text_method` arm, and the before/after
transition (65533 → 233, 65533 → 44) was caused solely by editing that arm. The
first edit (to the non-live copy) produced no change, which is itself the proof
that the probe was reaching real code rather than a stub.

Driver shape (scratchpad, not committed):

```
use compiler.frontend.core.*            # plus lexer/parser/ast/monomorphize
use compiler.frontend.core.interpreter.*
fn main():
    val r = core_interpret_expr("\"café,\".char_code_at(3)")
    print(val_get_int(r).to_text())
```

Loading the package standalone needs explicit wildcard imports of
`lexer`, `lexer_struct`, `lexer_types`, `lexer_chars`, `parser`, `parser_expr`,
`parser_primary`, `ast`, `ast_expr`, `ast_stmt`, `types`, `monomorphize` —
the package `__init__.spl` re-export graph is incomplete, which is a large part
of why this code has never been exercised from a test.

Regression guard: `test/01_unit/compiler/interpreter/text_char_code_at_codepoint_spec.spl`
(3 examples, 0 failures). Structural by necessity — see the header comment in
that file, and reason 1 above.

## Neighbours checked (the whole `eval_text_method` family, both copies)

The point of enumerating: this is a recurring defect family, and a sweep that
does not enumerate the family leaves siblings.

| method | indexing | verdict |
|---|---|---|
| `char_code_at` | was BYTE, now CHARACTER | **FIXED, both copies** |
| `char_at` | BYTE (`s[idx:idx+1]`) | **divergence, deliberately NOT changed — see below** |
| `byte_at` | BYTE | Correct. Deliberate, documented, matches all lanes. Absent from the live copy (follow-up above) |
| `len` | BYTE length | Correct — seed returns `s.len()` (bytes) |
| `substring` | BYTE range | Correct — seed explicitly documents byte indexing so a `len`/`index_of` result stays valid input |
| `slice` | BYTE range | Correct — same as `substring`; seed shares the arm |
| `index_of` / `find` / `find_str` | BYTE offset | Correct — seed scans `as_bytes()` windows |
| `last_index_of` / `rfind` | BYTE offset | Correct — seed uses `str::rfind` (byte offset) |
| `contains`, `starts_with`, `ends_with`, `replace`, `split`, `split_lines`/`lines`, `trim`/`strip`, `to_upper`, `to_lower`, `to_string`, `parse_int` | no index argument | Not applicable — no byte/char axis to get wrong |

### `char_at` — a real divergence, but the split is upstream

`char_at` is genuinely inconsistent **between the reference lanes themselves**:

- Seed: `s.chars().nth(idx)` — CHARACTER indexed.
- C runtime `rt_string_char_at`: `rt_string_new(s->data + index, 1)` — a raw
  one-byte slice, BYTE indexed.

The interpreter currently matches the **runtime/native** side. Changing it to
match the seed would break agreement with native/JIT, so it is left alone and
flagged here instead. This is not a defect this interpreter introduced, and it
must not be "fixed" on one side in isolation. A comment at the `char_at` arm
points back to this document — it now lives in
`_EvalOps/access_literal_assign_eval.spl:269-278` (it was in `eval_methods.spl`
when this was written; that file has since been deleted).

## Related / adjacent

A parallel lane has shown `for ch in <text>` iterates the **byte** count rather
than the character count (6 for `"café,"`, should be 5). That is the same
byte-vs-char confusion one level up in the same decode area. It is being handled
separately and is deliberately untouched here; the `char_code_at` fix does not
change loop lowering and the two do not overlap in code, but a full sweep of the
family should treat them together.

## Files changed

- `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` — the live copy; the fix that actually changed behaviour
- `src/compiler/10.frontend/core/interpreter/eval_methods.spl` — the second copy, fixed identically; `char_at` divergence documented in place. **DELETED later the same day in `f97dfbbb8ee`** once it was established that *all four* of its functions (`eval_method_call`, `eval_method_with_args`, `eval_array_method`, `eval_text_method`), not just `eval_text_method`, were shadowed by `_EvalOps` copies. The "fixed identically" edit recorded here was therefore a no-op on behaviour — which is exactly the finding in the section above, and is why the "no observable change" measurement in this document is the load-bearing evidence, not the source review.
- `test/01_unit/compiler/interpreter/text_char_code_at_codepoint_spec.spl` — new structural regression guard

## Follow-up status (updated 2026-08-01)

The follow-up filed above ("either de-duplicate `eval_text_method` or port the
missing arms into the live copy") is **done**: `f97dfbbb8ee` ported `byte_at`,
`slice`, `char_at`, `parse_int`, `to_upper`, `to_lower`, `to_string`, `find`,
`find_str`, `rfind` and `last_index_of` into the live
`_EvalOps/access_literal_assign_eval.spl` and deleted the dead duplicate. The
structural spec `text_byte_at_dispatch_spec.spl` — noted above as guarding the
copy that does not run — must be re-pointed at the live file, or it keeps
guarding nothing. Consolidated write-up and the doc-contamination audit:
`doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.
