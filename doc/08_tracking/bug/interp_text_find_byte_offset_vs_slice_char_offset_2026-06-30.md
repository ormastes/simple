# Bug: `text.find` returns a BYTE offset but `text.slice`/`text.len` use CHAR offsets

Status: **RESOLVED / CLOSED 2026-08-17** (was OPEN P2)

> **Closed on CONTENT + RUNTIME evidence, not on SHA ancestry.** The earlier
> "re-verified 2026-08-17 by source inspection (triage shard 02)" line was wrong:
> that shard confirmed only that `find` is byte-based, and inferred the mismatch
> from the doc's prose instead of checking what `slice`/`len` do TODAY.
>
> **`slice` and `len` are now byte-indexed too, so the unit mismatch is gone.**
> `src/compiler_rust/compiler/src/interpreter_method/string.rs`:
> - `"len" | "length" => Value::Int(s.len() as i64)` — BYTES.
> - the `"slice" | "substring"` arm now slices `s.as_bytes()` and carries an
>   explicit comment: *"BYTE-indexed, matching the JIT/native lane (`rt_slice`)
>   and this interpreter's own byte-valued `len` / `index_of`. Indexing by
>   character here made an index produced by `len`/`index_of` invalid input to
>   `slice`"* — i.e. this exact defect was diagnosed and deliberately fixed by
>   making the whole family consistently byte-indexed.
>
> **This doc's own reproducer now produces the expected result** (deployed seed
> `bin/release/x86_64-unknown-linux-gnu/simple`, `SIMPLE_EXECUTION_MODE=interpret`,
> 2026-08-17):
>
> ```
> $ bin/simple run /tmp/r4b.spl
> i=7
> out=MARKERxyz        <- expected "MARKERxyz"; the bug produced "RKERxyz"
> ```
>
> A second probe on the `café`/`Z` shape agrees: `len=9` (bytes), `find=5`
> (bytes), `slice(0, 5)="café"` — consistent, no corruption.
>
> **Residual, NOT this bug (not re-filed here):** `char_at`/`at` and
> `char_code_at` remain CHARACTER-indexed while `len`/`find`/`slice` are
> byte-indexed (`"caféZdef".char_at(3)` returns `é`, the 4th *char*, not the 4th
> byte). That is a separate, deliberately documented choice in the same file; if
> it is to be challenged it needs its own bug, with its own reproducer.

**Date:** 2026-06-30
**Severity:** Medium — silent data corruption. Mixing `find` with `slice`/`len`
(the natural "find a marker then slice from it" idiom) corrupts substring
extraction whenever the text before the marker contains any multibyte UTF-8
(e.g. an em-dash `—`, 3 bytes). ASCII-only inputs are unaffected, so it hides
until a non-ASCII char appears upstream.
**Component:** Rust seed interpreter — text intrinsics (`find` vs `slice`/`len`
unit mismatch).

## Reproducer

```simple
val s = "ab—cdMARKERxyz"     # em-dash is 3 bytes, 1 char
val i = s.find("MARKER")     # => 7  (BYTE offset)
print(s.slice(i, s.len()))   # => "RKERxyz"  (slice treats 7 as a CHAR offset)
# expected "MARKERxyz"
```

## Impact observed

The torch readiness specs
(`torch/dyn_sffi_ops_readiness_spec`, `torch/torch_training_seed_status_spec`,
`torch/torch_device_placement_status_spec`) read a library `.spl` file and
extract a function body via `find(marker)` + `slice(start, …)`. Library comments
contain em-dashes before the markers, so the body came back missing its leading
chars (`ensor_cuda…` instead of `fn tensor_cuda…`), failing `to_contain` checks.

## Workaround (LANDED)

Those specs now use a char-based `char_find` helper (scans with `slice` so the
returned offset is in the same char units as `slice`/`len`). No assertions
weakened.

## Proper fix (not done)

Make the text intrinsics consistent: either `find` should return a CHAR offset
(matching `slice`/`len`/`substring`), or provide a clearly-named byte/char pair.
Audit other `find`+`slice` call sites for the same latent skew.

## 2026-08-17 re-verification (lane m1_rust_interp) — ALREADY FIXED IN SOURCE

Classified by CONTENT (per session CORRECTIONS #1).

The reported asymmetry is gone: in
`src/compiler_rust/compiler/src/interpreter_method/string.rs` all three
operations are now consistently BYTE-indexed, so an index produced by `len` or
`find`/`index_of` is valid input to `slice`:

- `string.rs:21`  `"len" | "length" => Value::Int(s.len() as i64)`  — byte length
- `string.rs:44`  `"find_str" | "find" | "index_of"` — `s.find(&needle)` byte offset
- `string.rs:333` `"slice" | "substring"` — byte-indexed, with an explicit comment:

```
// BYTE-indexed, matching the JIT/native lane (`rt_slice`, which
// slices `s->data + begin` raw) and this interpreter's own
// byte-valued `len` / `index_of`. Indexing by character here made
// an index produced by `len`/`index_of` invalid input to `slice`:
// for "caféZdef" (9 bytes / 8 chars) `index_of("Z")` is 5, and a
// char-indexed `slice(0, 5)` wrongly yielded "caféZ".
```

That comment describes this doc's exact reproduction case and states the
resolution. A byte range that splits a multi-byte codepoint substitutes U+FFFD,
matching what the native lane emits for such a range, so the interpreter and the
compiled lane agree.

**Status: RESOLVED (stale doc)** — the chosen resolution was to make everything
byte-indexed (matching the native lane), not to make everything char-indexed.
