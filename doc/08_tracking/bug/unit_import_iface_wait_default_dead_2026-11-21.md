# Unit lane: the interface-import wait default is 0, so no importer waits

- **Status:** verification-pending (fix needs a Stage 2 rebuild)
- **Found:** 2026-11-21, provisional native group build (Stage 2 `0d8a3269bec`,
  per-file worker pool, 9 workers)
- **Symptom:**

```
AOT compile error in lib.nogc_sync_mut.io.external_text_io: unproven-call-origin:
MIR call target lacks proven source/runtime/foreign origin:
callee=lib.common.encoding.external_text.ExternalText.encoded_bytes
fn=lib.nogc_sync_mut.io.external_text_io.io_external_bytes
```

preceded in the same unit by
`[unit-tldr] import interface-hir miss reason=no-sidecar path=.../external_text.spl`.

## Cause

`fafa82e3c67` made an importing unit wait, up to
`SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS` (default 60 s), for a provider this build
will run. The budget was read as

```simple
(sosix_env_get_nullable("SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS") ?? "").to_i64() ?? 60000
```

(`driver_hir_pipeline_lowering.spl:1210`). On the native Stage 2 an
unparsable text converts to 0, not nil: `"".to_i64() ?? 60000` is 0 and
`"x".to_i64() ?? 60000` is 0. With the variable unset the budget is 0 and
`hir_unit_import_interface_load_v1` skips the wait. An importer that runs
before its provider published a `.hirkey` sidecar falls back to the TLDR
summary. A summary surface lists module-level callables only, so a method of
an imported class gets no call-origin row and codegen refuses the call.

`external_text.spl` does not import `external_text_io.spl`, and a later unit
in the same run logged `import interface-hir hit` for it: a working wait is
expected to cover this case.

## Repro (frozen Stage 2)

- One file: `val w: i64 = "".to_i64() ?? 60000` prints 0.
- Mutual-import fixture (`cfx/a.spl` and `cfx/b.spl` each declare a class and
  call a method of the other's), `--threads 2`: `interface-hir miss
  reason=no-sidecar` for `a.spl`, then `unproven-call-origin:
  callee=cfx.a.CfxTag.plus_one`. Wall time 28 s with the variable unset and
  36 s with `SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS=8000` (one run each): the wait
  runs only when the variable is set.

## Fix

`hir_unit_import_iface_wait_ms_v1` (`driver_hir_cache.spl`) checks the text
itself: unset, blank or non-numeric gives 60000; digits give their value.
Spec: `unit_import_interface_hir_spec.spl`, "interface import wait budget".
The spec was not run (no full CLI on this host); the function was compiled
and run standalone on the frozen Stage 2 with the spec's six inputs.

Not verified: that the 1258-module build then reaches `interface-hir hit` for
`external_text.spl`. Setting `SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS=60000` in the
environment gives the frozen Stage 2 the same budget without a rebuild.

## Open

- The fixture above still fails with a working wait: in an import cycle one
  side always runs first, and the summary fallback has no method rows.
  `SIMPLE_FILE_WORKERS=0` builds it.
- The same `text.to_i64() ?? <default>` shape appears with a `-1` default in
  `native_file_worker_v1.spl`, `native_mir_shard.spl`,
  `driver_unit_order_index_v1.spl` and others. Each reads 0, not -1, for an
  unparsable field on the native compiler. Not audited here.
