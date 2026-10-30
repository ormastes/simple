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
