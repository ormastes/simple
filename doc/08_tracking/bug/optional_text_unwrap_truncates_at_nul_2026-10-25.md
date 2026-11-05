# Native `text?` unwrap truncates at the first NUL byte

- **Status:** open (compiler). Workaround on the Stage 3 hello-world path:
  `src/app/compiler_entrypoint/inventory_scratch.spl` uses `content ?? ""`.
  Tagged `@workaround bug=optional_text_unwrap_truncates_at_nul_2026-10-25`.
- **Found:** on the Phase 3 Stage 3 hello world. This was the next failure
  after `transient_promote_struct_param_copy_dangles_2026-10-25.md` was fixed.

## Symptom

```
SCV-E-ADMISSION: snapshot-index-drift:src/lib/scv/identity_corrections.spl
```

That file contains 6 literal NUL bytes; the first is at offset 4158. The
inventory recorded `byte_count=4158` and the sha256 of the first 4158 bytes.
The snapshot reads the same file as `[u8]` and gets 11465 bytes, so the two
disagree. Of 18,303 src rows, this was the only mismatch.

## Root cause

In `HirExprKind.Unwrap` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
`case Unwrap`), a `text` payload sets `uw_is_text` and calls
`option_text_value` (`50.mir/_MirLoweringExpr/method_calls_literals.spl:772`).
That emits `rt_interp_cstr` on the payload. The runtime string
(`rt_file_read_text_at_checked` builds it with `rt_string_new(buffer, n)`,
full length) is turned into a C string, and any later `len` or digest stops
at the first NUL.

Stage 2 (`S/r27/stage2-simple`) native probe:

| form | len (file is 11465 bytes) |
|---|---|
| `t!` | 4158 |
| `match t: case Some(s)` | 4158 |
| `if val s = t` | 4158 |
| `t.unwrap()` | 4158 |
| `t ?? ""` | 11465 |

## Fix direction

Decode the `text` payload of an Option without a C-string round trip: keep
the runtime string handle, as `??` already does. The fix belongs in
`option_text_value` and its callers. Search the tree for `text?` unwraps on
binary-capable content after the fix.

Spec: `test/01_unit/compiler/50.mir/optional_text_unwrap_nul_spec.spl`. It is
red only natively.

## mirp2-G 2026-11-05: runtime root fix (pending native verification)

Native probe (s3_fable44, Windows): file `ab\0cd` read via
`rt_file_read_text_at_checked` and unwrapped; a NUL literal probe
(`"ab" + "\x00" + "cd"`) gave `4` for **all five** forms including `??`, so `??`
is not immune either: every text decode in this lane ends at `rt_interp_cstr`
(RtCoreString.data), and length is then recomputed with `rt_strlen`/`strlen`.

Root cause is the length recovery, not the unwrap: `rt_strlen` and the raw
fallback of `rt_string_len` called `strlen` even when the raw pointer is exactly
the `data` member of a live registered heap string. Fix
(`src/runtime/runtime_native.c`): `rt_core_string_from_data_pointer` (same
validation order as `rt_core_transient_text_data_pointer`: alignment/low-address
rejects, registry membership before any header read) and both functions return
the owner's `len`. This covers `.len()`, the `rt_strlen + rt_string_new` re-tag
(`tag_str_local_if_raw`) and the text extern ABI pair. Rust runtime has no raw
`char*` fallback (returns -1), so no twin divergence.

Spec: `src/runtime/test/rt_string_len_data_pointer_nul_selfcheck.c` (links the
real runtime_native.c; red on the old code: `rt_string_len(raw) == 5` failed,
green after). Existing `test/01_unit/compiler/50.mir/optional_text_unwrap_nul_spec.spl`
stays the native gate.

Separate, unfixed: a NUL inside a string *literal* (`"\x00"`) is a `.rodata`
C string, so its length is lost at the literal itself.

Next step: rebuild a native probe against this runtime (needs >12 GB free on C:,
it had 6.3 GB) and run the spec natively; then drop the
`inventory_scratch.spl` `?? ""` workaround and close.
