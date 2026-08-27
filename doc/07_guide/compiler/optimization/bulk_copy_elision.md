# Bulk-Copy Elision (SG-1.3)

A quarantined C-backend MIR optimization that formerly collapsed a contiguous element-wise
array copy into a single `memmove`. It is **disabled**, including when the legacy environment
flag is set, because distinct MIR base locals do not prove non-overlapping storage.

## Enabling

```bash
SIMPLE_MIR_BULK_OPS=1 bin/simple compile prog.spl --emit-c   # remains disabled
```

All flag values are exact passthroughs. `mir_bulk_ops_enabled()` returns false,
`apply_bulk_recognizers()` returns its module unchanged, and the direct
`elide_bulk_copy()` adapter returns its function unchanged.

```
if backend_name == "c" and mir_bulk_ops_enabled(): # currently always false
    optimized = apply_bulk_recognizers(optimized)
```

## Why it is quarantined

A lowered array copy appears in MIR as a run of 4-instruction units, one per element:

```
GEP gs = src[i]      Load ld = *gs      GEP gd = dst[i]      Store *gd = ld
```

The dormant matcher can recognize that shape, and the C backend can lower an active intrinsic to:

```c
memmove((void*)dst, (void*)src, count * 8);
```

(element stride is 8 bytes, matching the GEP lowering `(char*)base + idx*8`).

Structural matching, H1 temp-liveness, and H2 element-size checks are not enough. Two distinct
base LocalIds may alias overlapping spans. A forward element loop can read a value written by
the prior iteration, while `memmove` snapshots the original source semantics. Replacing one
with the other can therefore change results.

Reactivation requires a dominance-scoped region/alias proof that the complete source and
destination byte spans are disjoint, plus the existing conditions below and semantic
differential coverage. Until then it never fires.

## Dormant structural conditions

The dormant matcher checks these conditions, but they do not authorize a rewrite without the
missing alias proof:

1. **Canonical consecutive run** — the units are exactly back-to-back, nothing interleaved
   (so the element-wise version cannot observe a half-copied state that `memmove` wouldn't).
2. **Contiguous from 0** — indices are `0,1,…,k-1` with `k >= 2`.
3. **`dst[i] = src[i]`** — same index on both sides (not `dst[5] = src[2]`), `src_base != dst_base`.
4. **H1 — temporaries dead outside the run.** The element pointers and loaded values must not be
   referenced by any other instruction or terminator (eliding deletes their defining ops).
5. **H2 — 8-byte elements.** Each loaded element type must be positively confirmed 8 bytes
   (`MirType.primitive_size() == 8`). A sub-8-byte element (i32/i16/bool/f32) is rejected: the
   per-element Store writes `sizeof(ty)` bytes, but `memmove` would copy the full `count*8`.

## Quarantine evidence

```bash
SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed \
  bin/simple run src/compiler/60.mir_opt/bulk_copy_elision_spec.spl
```

The spec requires canonical positive witnesses and former rejection cases alike to remain
unchanged. See also `bulk_ops_flag_spec.spl` (legacy flag cannot activate the pass) and
`test/01_unit/compiler/backend/c_backend_bulk_copy_memmove_spec.spl` (the memmove lowering).

## Scope & limitations

- The active `bulk_copy` intrinsic remains a C-backend lowering surface, but no Simple MIR pass
  currently produces it.
- The self-hosted compiler is dormant relative to the Rust seed, so this path is **not** exercised
  by `bin/simple test` or by seed-run benchmarks; it is verified at the MIR unit level.
- `bulk_fill` / `bulk_cmp` are not elided; bulk copy is also disabled.
- The older additive `optimize_bulk_copy` recognizer (index-blind, emits the no-op
  `bulk_copy_hint`) is retained as an advisory pass but is **not** on the pipeline path; never
  lower its hint to the active intrinsic without the guards above — see bug
  `sg13_bulk_copy_recognizer_index_blind`.
