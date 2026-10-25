# `d[k] ?? default` on a Dict<_, text> miss returns raw 0, not the default
## Open 2026-10-25 — compiler fix in `50.mir/_MirLoweringExpr/expr_dispatch.spl`; takes effect on the Phase 3 self-rebuild

Date: 2026-10-25. Lane: Phase 3 bootstrap (run-27e), compiler-fix agent.

## Symptom

`ctx.config["compiler_source_entry"] ?? ""` (`80.driver/driver_phase_gates.spl:32`)
returned a NULL text on a missing key, so phase 1 reported
`compiler entry '' collected zero source files`. 44 `config[k] ?? d` sites in
`src/compiler/80.driver` have this shape (`mcdc_mode ?? "off"` -> NULL, so
`== "off"` is false).

## Root cause

`??` lowered its left operand with plain `lower_expr`. For a `d[k]` index read
that goes to `lower_dict_runtime_read(..., as_option: false)`, which decodes the
raw word BEFORE the nil test:

```
rt_dict_get -> rt_interp_cstr(raw) -> rt_is_some -> payload
```

On a miss `rt_dict_get` returns `RT_NIL` (3); `rt_interp_cstr(3)` is NULL and
`rt_is_some(0)` is true, so the present branch returns 0. `d.get(k)` did not
have this MISS bug: it already reads with `as_option: true`, which routes the miss
sentinel around the decode (`dict_get_preserve_flat_nil`,
`native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`).

## Fix

`lower_index_expr` takes `nil_probe: bool = false`, which is consulted only on
its runtime-dict branch and forwarded to `lower_dict_runtime_read` as
`raw_probe`. With `raw_probe` set AND the declared value type V resolved, the
reader returns the UNDECODED
`rt_dict_get` word, marks it a runtime value, records `Optional(V)` on it
(the `??` present branch takes its decode type from that), and carries the
store-observed struct name (#189 parity). With V unresolved it falls through to
the old decoded read, so the miss defect persists only there.
The `??` arm lowers its left operand through the new
`lower_optional_probe_operand`, which sets `nil_probe` for a `d[k]` read and
otherwise calls `lower_expr` unchanged. `rt_is_some` then tests the raw word,
so a miss stays 3. The `??` present branch, `decode_runtime_value` on a
runtime-value local, is the single decode.

The first draft reused the decoded `as_option` lane that `d.get(k)` uses. The
review rejected it: under `??` that lane decodes a hit twice. Stage 2 measured
`di.get("five") ?? -77` -> `0` and `di.get(wide) ?? -77` -> `wide >> 3`, so
routing `d[k]` through it would have regressed every non-zero i64 hit.

Non-dict index reads are unchanged. The static-scalar mark that `lower_expr`
sets for declared scalar-array reads is kept. No nil acceptance is widened:
the change only stops a decode from destroying an existing nil.

## Still open (not fixed here)

- **`d.get(k) ?? x` on a `Dict<_, i64>` decodes a hit twice.** Measured on
  Stage 2: a stored 5 comes back as 0, and a stored `1 << 40` (inline immediate) comes back as
  `1 << 37`. The `as_option` reader decodes and then marks the merged local as
  a runtime value, so the `??` present branch decodes it again. Text is
  unaffected because `rt_interp_cstr` is idempotent on a raw `char*`. The
  existing `native_dict_get_miss_sentinel_class_spec.spl` only probes a stored
  0, so it cannot see this.
- **`d[k].?`.** On Stage 2 a miss took the present branch. The ExistsCheck
  present branch has the same decode as `??`, but its result type comes only
  from the `.?` annotation, with no Str widening. Feeding it the raw word was
  not proven safe, so `.?` is left as it was.
- **`if val x = d[k]`.** The parser desugars it to a plain `val x = d[k]`
  binding plus `x != nil`, so the decode happens in the binding. On Stage 2 a
  miss took the present branch, and a HIT bound a decimal handle
  (`IFVAL-HIT-195021790629088`).
- **`match d[k]:` scrutinee and `d[k] == nil`.** Not examined.
- **List index `xs[i] ?? x`.** Not applicable: a list index has no miss
  sentinel, and an out-of-range read is not nil.

## Verification

- Red: Stage 2 builds the spec fixture. `dt["miss"] ?? "dflt"` printed an
  empty line, `di["miss"] ?? -77` printed `0`, and the struct-field form
  `ctx.config["compiler_source_entry"] ?? "dflt"` printed an empty line. The
  hits (`yes`, `[]`, `0`, `5`, heap-boxed `2^62`, field `on`) and the
  `dt.get("miss") ?? "dflt"` control were right.
- The patched modules pass Stage 2 parse and HIR (`src/app/zz_p3c/mc.spl`
  entry, 463-module closure).
- Green: deferred to the Phase 3 self-rebuild, because Stage 2 has the old
  lowering built in. Spec:
  `test/01_unit/compiler/codegen/native_dict_index_coalesce_miss_spec.spl`.

Related: `optional_text_unwrap_truncates_at_nul_2026-10-25.md` (pushunwrap
lane, the unwrap decode). This fix does not touch that path.
