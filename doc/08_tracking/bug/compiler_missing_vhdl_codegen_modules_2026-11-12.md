# Integration specs import product modules that do not exist (2026-11-12)

Status: open
Area: src/compiler (HWIR/VHDL codegen modules), src/app/spipe, src/lib std.time

## Symptom

A cluster of compiler-dir integration specs fails at load time under both the
seed and (for the module files, which are absent from the tree) the pure-Simple
toolchain, with either

```
error: runtime: Module "<parent>" does not export '<name>'
error: semantic: Cannot resolve module: <path>
```

and the harness then reports `test-runner: no examples executed` (fail-closed).

### Missing HWIR -> VHDL codegen modules (19 GHDL specs, 0 executed each)

`test/02_integration/compiler/riscv_scalar_*_ghdl_spec.spl` import one of these,
none of which exist anywhere under `src/`:

- `compiler.backend.riscv_scalar_decoder_to_vhdl` (decoder_ghdl)
- `compiler.mir.hwir.riscv_scalar_decoder` (decoded_uop_skid_ghdl,
  pending_provider_owner_ghdl)
- `compiler.mir.hwir.riscv_scalar_runtime_alu` (runtime_alu_ghdl)
- `compiler.backend.riscv_scalar_runtime_alu_pipeline_to_vhdl`,
  `riscv_scalar_runtime_lsu_composition`, `riscv_scalar_runtime_lsu_to_vhdl`,
  `riscv_scalar_runtime_m_provider`, `riscv_scalar_runtime_mul_low_provider`,
  `riscv_scalar_runtime_pipeline_v3..v9_rvfi_to_vhdl`,
  `riscv_scalar_runtime_stateful_v2_to_vhdl` (the remaining runtime_*_ghdl specs)

Sibling modules DO exist (`riscv_scalar_hwir_to_vhdl.spl`,
`riscv_scalar_product_to_vhdl.spl`, `riscv_scalar_fence_owner_to_vhdl.spl`,
`riscv_scalar_csr_owner_to_vhdl.spl`, ...), so this looks like a set of
decoder/runtime codegen units that were planned or removed without updating
the specs. `git log --all -- <path>` shows no history for these names.

### Other unresolvable imports

- `test/02_integration/compiler/demand_compile_observability_integration_spec.spl`:
  `use app.spipe.testing.*` — no `testing` module under `src/app/spipe/`.
- `test/02_integration/compiler/driver/parser_external_inspection_process_v1_spec.spl`:
  `use std.time.sleep_ms` — no `std.time` module; the live sleeps are
  `std.nogc_sync_mut.src.time.sleep_ms` / `nogc_async_mut_noalloc/.../sleep_ms`.

## Root cause

Specs were committed (or left) referencing product modules that are not in the
tree. Either the modules were never landed, were removed in a refactor without
updating the specs, or live under different names/paths now.

## Unblock

Land the missing codegen modules, or repoint the specs at the modules that
superseded them (and delete specs whose subject was intentionally dropped).
For `app.spipe.testing` and `std.time.sleep_ms`, fix the import paths or add
the intended modules. Until then these specs cannot execute.

## PARTIALLY FIXED 2026-11-13 (wave-2 deep-fix lane, work/compiler-seed-deepfix-20261113)

### std.time.sleep_ms — FIXED
`test/02_integration/compiler/driver/parser_external_inspection_process_v1_spec.spl`
now imports `std.nogc_sync_mut.src.time.{sleep_ms}` (the live module,
src/lib/nogc_sync_mut/src/time.spl:86). The spec LOADS AND EXECUTES (was:
0 examples, hard import error). Its single example then fails deeper with
"OwnedProcessV3 opaque adapter is unavailable in the interpreter; it requires
the native runtime provider" -- the spec spawns real processes, which the
seed-run interpreter cannot provide (the packet-level unit spec
test/01_unit/lib/common/process_inspection_v1_spec.spl passes 3/3 on the same
interpreter). That remainder is an infrastructure requirement, not an import
defect.

### app.spipe.testing — TRIAGE INCOMPLETE, spec unrescuable in this lane
Removing the dead `use app.spipe.testing.*` wildcard (nothing from it is
used; describe/it/expect come from std.spec) exposes a SECOND missing module
the triage did not record: `app.perf.demand_compile_receipt`
(`demand_compile_receipt_create_v1` / `demand_compile_receipt_validate_v1`
exist NOWHERE under src/ -- verified by content search). The spec's subject
(the demand-compile receipt producer) was never landed; the spec cannot load
without implementing it, which is feature work, not a bug fix. Change
reverted; this record now tracks both missing modules. Sibling
`test/02_integration/compiler/cache/reverse_reference_projection_receipt_spec.spl`
imports the same dead `app.spipe.testing.*` and is unaffected by this lane.

### Missing HWIR -> VHDL codegen modules (19+ GHDL specs) — CONFIRMED, owner decision required
All 13 missing module families re-verified absent under any path
(`find src -name <module>.spl` and content search; the only v9 hit is the
unrelated `src/app/verify/riscv_scalar_runtime_pipeline_v9_formal_bundle.spl`):
riscv_scalar_decoder_to_vhdl, compiler.mir.hwir.riscv_scalar_decoder,
riscv_scalar_runtime_alu, riscv_scalar_runtime_alu_pipeline_to_vhdl,
riscv_scalar_runtime_lsu_composition, riscv_scalar_runtime_lsu_to_vhdl,
riscv_scalar_runtime_m_provider, riscv_scalar_runtime_mul_low_provider,
riscv_scalar_runtime_pipeline_v3..v9_rvfi_to_vhdl,
riscv_scalar_runtime_stateful_v2_to_vhdl. `git log --all` shows no history for
any of these names and no superseding module exists under src/. Landing 13
hardware codegen units is a multi-week feature effort for the hwir/backend
owner; deleting the specs needs an intentional-drop decision from the same
owner. This lane documents precisely; it does not guess.
