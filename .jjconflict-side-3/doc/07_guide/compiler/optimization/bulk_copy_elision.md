# Bulk-Copy Elision (SG-1.3)

A C-backend MIR optimization that collapses a contiguous element-wise array copy into a
single `memmove`. It is **default-OFF**, **C-backend only**, and **sound by strictness**.

## Enabling

```bash
SIMPLE_MIR_BULK_OPS=1 bin/simple compile prog.spl --emit-c   # C backend only
```

Default (flag unset / `=0`) is an exact passthrough — no MIR change, identical codegen. The
optimization is gated in `optimize_module_for_backend` (`60.mir_opt/mir_opt/mod.spl`):

```
if backend_name == "c" and mir_bulk_ops_enabled():
    optimized = apply_bulk_recognizers(optimized)   # runs elide_bulk_copy per function
```

## What it does

A lowered array copy appears in MIR as a run of 4-instruction units, one per element:

```
GEP gs = src[i]      Load ld = *gs      GEP gd = dst[i]      Store *gd = ld
```

`elide_bulk_copy` (`60.mir_opt/optimization_passes_part2.spl`) replaces a qualifying run with one
intrinsic, which the C backend (`70.backend/.../c_backend_translate_ops.spl`, `emit_bulk_copy`)
lowers to:

```c
memmove((void*)dst, (void*)src, count * 8);
```

(element stride is 8 bytes, matching the GEP lowering `(char*)base + idx*8`).

## When it fires — the soundness conditions

It fires **only** when every condition holds; otherwise the function is returned unchanged
(a missed copy is a perf miss, never a miscompile):

1. **Canonical consecutive run** — the units are exactly back-to-back, nothing interleaved
   (so the element-wise version cannot observe a half-copied state that `memmove` wouldn't).
2. **Contiguous from 0** — indices are `0,1,…,k-1` with `k >= 2`.
3. **`dst[i] = src[i]`** — same index on both sides (not `dst[5] = src[2]`), `src_base != dst_base`.
4. **H1 — temporaries dead outside the run.** The element pointers and loaded values must not be
   referenced by any other instruction or terminator (eliding deletes their defining ops).
5. **H2 — 8-byte elements.** Each loaded element type must be positively confirmed 8 bytes
   (`MirType.primitive_size() == 8`). A sub-8-byte element (i32/i16/bool/f32) is rejected: the
   per-element Store writes `sizeof(ty)` bytes, but `memmove` would copy the full `count*8`.

## Verifying

```bash
SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed \
  bin/simple run src/compiler/60.mir_opt/bulk_copy_elision_spec.spl   # firing + non-firing
```

The non-firing tests (non-contiguous indices, `dst!=src`, interleaved op, temp-used-after,
escaping pointer, sub-8-byte element) are the **safety proof** — each asserts the block is left
unchanged. See also `bulk_ops_flag_spec.spl` (flag wiring) and
`test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl` (the memmove lowering).

## Scope & limitations

- C backend only. The active `bulk_copy` intrinsic traps/links-errors on other backends, so the
  pass is never run for them.
- The self-hosted compiler is dormant relative to the Rust seed, so this path is **not** exercised
  by `bin/simple test` or by seed-run benchmarks; it is verified at the MIR unit level.
- `bulk_fill` / `bulk_cmp` are **not** elided — only copy is currently sound.
- The older additive `optimize_bulk_copy` recognizer (index-blind, emits the no-op
  `bulk_copy_hint`) is retained as an advisory pass but is **not** on the pipeline path; never
  lower its hint to the active intrinsic without the guards above — see bug
  `sg13_bulk_copy_recognizer_index_blind`.
