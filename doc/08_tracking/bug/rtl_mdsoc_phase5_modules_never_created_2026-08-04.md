# RTL MDSOC reorg Phase 5 modules were never created — 68 system examples red
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Re-verified 2026-08-10

Fresh independent check (`test -f` on each of the 8 asserted SA-3/SA-4
module paths, plus `/usr/bin/grep -rl "# capsule:" src/compiler/70.backend/backend/`):
all 8 modules are still absent from the tree exactly as documented, and zero
files anywhere under `src/compiler/70.backend/backend/` carry a `# capsule:`
marker (still 0, not even the "cheap half" landed). `src/hardware/fpga_linux/`
was not independently re-listed but the module-path checks above are
sufficient — no new evidence of any Phase 5 SA-3/SA-4 work having landed since
2026-08-04. Characterization is confirmed accurate and unchanged: this is
genuine unbuilt design-owned feature work, correctly ARCHITECTURAL/OPEN, not a
defect. No code change made. Status stays OPEN.

## Triage 2026-09-13
Reconfirmed: Phase 5 RTL MDSOC reorg modules still never created per this
record, 68 system examples affected. Large module-creation feature work,
not a quick fix. Left OPEN, no code change attempted.
## Triage 2026-09-13 (BUGFIX-12 shard 22)

Still genuine unbuilt design-owned feature work (Phase 5 RTL MDSOC reorg), not
a defect — a whole reorg phase, not a shard-scale fix. No change made.
Leaving OPEN.


## Resolution 2026-11-05 (RTL lane, PR #6979 — wait verification)

State at the release/1.0.0 tip was better than this record: the SA-3 split
modules already exist under `src/lib/hardware/fpga_linux/` (orchestrator,
data, manifest + the 13-line re-export facade). What was still missing, and
what this lane landed per `doc/05_design/app/riscv/rtl_riscv_mdsoc_capsules.md`:

- **SA-4 plug-in stubs created** (fail-closed, honest, no fabricated
  behavior): `src/plugins/backend_vhdl/vhdl/vhdl_emit_{fp,simd,cache,hart}_stub.spl`,
  each a one-function module whose body returns a VHDL comment line
  (`-- VHDL-EMIT-…-STUB-NOT-IMPLEMENTED`) with a TODO(Feature A/B) link, plus
  the `# capsule:` markers. `vhdl/__init__.spl` and `vhdl/mod.spl` re-export
  all four.
- **SA-2 capsule markers** added to the 9 existing emitter files, with the
  marker values from the design's capsule table.
- **AC-4 plan annotations**: `<!-- capsule: … -->` comments added to each of
  the 8 agent sections of `doc/03_plan/hardware/pure_simple_vhdl_riscv_gap_spawn_plan.md`
  plus a preamble mapping block (per-agent mapping taken from the design doc's
  8-agent table).
- **Spec repairs to the landed SA-3 reality** (same class as bug 2's
  resolution): `fpga_linux_split_spec.spl` imported
  `hardware.fpga_linux.riscv_fpga_linux`, which still resolves to the old
  6990-line monolith at `src/hardware/fpga_linux/` — switched to the
  `std.hardware.fpga_linux.riscv_fpga_linux` facade (the import path the
  production driver `riscv_fpga_bundle.spl` already uses). Its AC-7 script
  paths were also stale (`scripts/rtl_riscv*.shs` → `scripts/rtl/…`, the path
  every other consumer uses).
- **debug_sidecar_json_order_spec.spl** was not executable at all (cover
  admission failure — no `# @req`/`# @cover` header). Added the standard
  header; the 7 source-contract checks now execute and PASS.

**Verification (seed interpreter):** rtl_mdsoc_capsule_boundary 22/22,
rtl_mdsoc_plugin_stubs 20/20, fpga_linux_split 19/19 (all were red before),
debug_sidecar_json_order 7 passed / 9 failed-of-16.

**Left red, by design of the specs themselves:** the 9 debug_sidecar
failures are fail-closed tripwires over `build/rtl_linux/generated_{rv32,rv64}`
that turn green only after a real generation run
(`scripts/rtl/rtl_riscv{32,64}_linux_generated.shs`). That lane requires an
LLVM-capable Simple binary; none exists in the RTL worktree, so host-side
generation verification is pending — this is the "wait verification" state.
The old monolith at `src/hardware/fpga_linux/riscv_fpga_linux.spl` is retained
(verified consumers: test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl,
test/01_unit/compiler/backend/vhdl_backend_spec.spl, both green).

## Premise triage 2026-11-05 (mirp2-F, origin/release/1.0.0 @ 27e65c24371-era)
Premise gone: `src/plugins/backend_vhdl/vhdl/vhdl_emit_{fp,simd,cache,hart}_stub.spl`
all exist on release/1.0.0 (PR #6979). Row already `fixed`; only the
host-side native/synthesis verification noted in bug_db remains. No action.
