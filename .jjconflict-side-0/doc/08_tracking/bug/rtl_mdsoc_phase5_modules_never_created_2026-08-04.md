# RTL MDSOC reorg Phase 5 modules were never created — 68 system examples red

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

Four specs under `test/system/compiler/` are red, 68 examples in total.
Measured with:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
  test/system/compiler > /tmp/sys.log 2>&1
```

| spec | passed | failed |
|------|--------|--------|
| `test/system/compiler/rtl_mdsoc_capsule_boundary_spec.spl` | 0 | 22 |
| `test/system/compiler/rtl_mdsoc_plugin_stubs_spec.spl` | 0 | 20 |
| `test/system/compiler/fpga_linux_split_spec.spl` | 0 | 16 |
| `test/system/compiler/debug_sidecar_json_order_spec.spl` | 12 | 10 |

Every failure has the same shape — a file-presence or marker-presence predicate
returning false:

```
✗ AC-1: fpga_linux_orchestrator.spl exists with capsule marker vhdl.emit.control
    expected false to equal true
✗ AC-5: vhdl_emit_fp_stub.spl exists with capsule marker vhdl.emit.data.fp
    expected false to equal true
```

Expected: the named module exists and carries a `# capsule: <name>` line in its
first 40 lines. Actual: the module does not exist at all.

## Root cause

The specs are acceptance criteria for `#rtl-mdsoc-reorg` Phase 5 (SA-3 and
SA-4), written ahead of the implementation. The implementation never landed.

Modules asserted but absent from the tree (verified by `test -f` on each path
extracted from the spec sources):

- `src/hardware/fpga_linux/fpga_linux_orchestrator.spl` (SA-3)
- `src/hardware/fpga_linux/fpga_linux_data.spl` (SA-3)
- `src/hardware/fpga_linux/fpga_linux_manifest.spl` (SA-3)
- `src/hardware/fpga_linux/riscv_fpga_linux.spl` (SA-3 re-export facade)
- `src/compiler/70.backend/backend/vhdl/vhdl_emit_fp_stub.spl` (SA-4)
- `src/compiler/70.backend/backend/vhdl/vhdl_emit_simd_stub.spl` (SA-4)
- `src/compiler/70.backend/backend/vhdl/vhdl_emit_cache_stub.spl` (SA-4)
- `src/compiler/70.backend/backend/vhdl/vhdl_emit_hart_stub.spl` (SA-4)

`debug_sidecar_json_order_spec.spl` is the fourth victim of the same absence —
its AC-3 group asserts key ordering *inside* `fpga_linux_manifest.spl` and
inside the `.debug.json` that module is supposed to emit:

```
✗ AC-3: fpga_linux_manifest.spl contains reportMarkers key string
    expected false to equal true
✗ AC-3: RV32 generated debug.json has reportMarkers key
    expected -1 to be greater than -1
```

The `-1` is `index_of` on empty content — the file it reads does not exist, so
every ordering comparison degenerates to `-1 < -1`.

`src/hardware/fpga_linux/` currently holds exactly one file,
`generate_riscv_fpga_bundle.spl` — the split the specs describe was never
performed.

Separately, the nine emitter modules that *do* exist all carry zero
`# capsule:` markers, so `rtl_mdsoc_capsule_boundary_spec.spl` AC-1 fails on
them too:

```
src/compiler/70.backend/backend/vhdl_backend.spl
src/compiler/70.backend/backend/vhdl/{vhdl_builder,vhdl_helpers,vhdl_memory_templates,vhdl_testbench,mod,__init__}.spl
src/compiler/70.backend/backend/vhdl_type_mapper.spl
src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl
```

Contract per `rtl_mdsoc_capsule_boundary_spec.spl` docstring: emitter files
carry `# capsule: vhdl.emit.<name>`, re-export facades carry
`# capsule: re-export`.

Design/requirements references named by the specs:
`doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md`,
`doc/05_design/rtl_riscv_mdsoc_capsules.md`.

## Why not fixed now

This is unbuilt feature work, not a defect. Making the specs green means
performing the Phase 5 SA-3 module split and authoring the four SA-4 plug-in
stub modules — a design-owned change to the VHDL backend and the FPGA/Linux
bundle path, well outside a test-repair lane. Adding the `# capsule:` markers
to the nine existing emitters is the one cheap half, but landing it alone would
turn `rtl_mdsoc_capsule_boundary_spec.spl` from 22 red to ~13 red while leaving
the other two specs untouched, so it should go with the reorg it documents.
