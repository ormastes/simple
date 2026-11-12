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
