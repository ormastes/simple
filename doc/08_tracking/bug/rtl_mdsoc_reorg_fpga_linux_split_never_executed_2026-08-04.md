# `#rtl-mdsoc-reorg` was specced TDD-red and never executed — 94 permanently-red examples per tree (2026-08-04)

**Status:** OPEN
**Found:** 2026-08-04
**Class:** specced-but-unimplemented refactor programme. **94 failing examples**
in `test/system/compiler/` (measured: 939 total, 803 passed, 136 failed — the
RTL/VHDL family is 94 of those 136), duplicated in `test/03_system/compiler/`.

## Programme-wide census (`test/system/compiler`, 2026-08-04)

| spec | failed | blocked on |
|------|--------|-----------|
| `rtl_mdsoc_capsule_boundary_spec.spl` | 22 | `vhdl/vhdl_emit_*_stub.spl` |
| `rtl_mdsoc_plugin_stubs_spec.spl` | 20 | the 4 plug-in stubs (Phase 5 SA-4) |
| `fpga_linux_split_spec.spl` | 16 | the 3 fpga_linux capsules (Phase 3 SA-3) |
| `vhdl_source_facade_spec.spl` | 12 | facade split |
| `debug_sidecar_json_order_spec.spl` | 10 | `fpga_linux_manifest.spl` (SA-3) |
| `pure_simple_vhdl_source_of_truth_spec.spl` | 6 | — |
| `rtl_mdsoc_byte_equal_spec.spl` | 4 | SA-1 baseline |
| `vhdl_backend_cli_smoke_spec.spl` | 2 | — |
| `vhdl_mir_backend_{multi_output,call_port_map}_spec.spl` | 1 + 1 | — |
| **total** | **94** | |

**These specs are intentionally red and say so in prose but do not mark
themselves `pending()`.** `rtl_mdsoc_plugin_stubs_spec.spl:31` states verbatim:

> TDD-red: these files do not exist before Phase 5 SA-4 runs.

Meanwhile `rtl_mdsoc_byte_equal_spec.spl:85,92` in the *same programme* does use
`pending("SA-1 baseline gate — ...")` correctly, so only 4 of its examples fail
instead of all of them. **Applying the same `pending()` treatment to the other
specs in the programme would remove ~90 permanently-red examples from every run
without weakening a single assertion** — the gate simply becomes explicit
instead of silent. That, not implementing the refactor, is the cheap correct
next step, and it is a decision for the `#rtl-mdsoc-reorg` owner.

The missing plug-in stubs are confirmed absent: `src/compiler/70.backend/backend/
vhdl/` exists and is well-populated (~20 modules), but contains **no**
`vhdl_emit_fp_stub.spl`, `vhdl_emit_simd_stub.spl`, `vhdl_emit_cache_stub.spl`
or `vhdl_emit_hart_stub.spl`, and no non-`_stub` equivalent of any of them.

## Original finding — the FPGA-Linux capsule split (26 of the 94)

## Symptom

```
FAIL  test/03_system/compiler/fpga_linux_split_spec.spl        (0 passed, 16 failed)
FAIL  test/03_system/compiler/debug_sidecar_json_order_spec.spl (12 passed, 10 failed)
```

Both specs assert against three capsule files that do not exist:

```
$ ls src/hardware/fpga_linux/
generate_riscv_fpga_bundle.spl          # 41 lines — the only file there
```

Expected by the specs (`fpga_linux_split_spec.spl:1-4`, `debug_sidecar_json_order_spec.spl:1-2`):

- `src/hardware/fpga_linux/fpga_linux_orchestrator.spl`
- `src/hardware/fpga_linux/fpga_linux_data.spl`
- `src/hardware/fpga_linux/fpga_linux_manifest.spl`
- `src/hardware/fpga_linux/riscv_fpga_linux.spl` (as a <30-line facade)

## Root cause (what is PROVEN)

1. **The split is a planned refactor that has not been performed, and the specs
   say so themselves.** `fpga_linux_split_spec.spl:11` carries
   `**Status:** Draft`, and `debug_sidecar_json_order_spec.spl:127` guards every
   assertion with `check_msg(rt_file_exists(path), "file not found (SA-3 not run
   yet): " + path)` — SA-3 being the phase of `#rtl-mdsoc-reorg` that was
   supposed to produce these files. The specs were written spec-first against
   `doc/05_design/rtl_riscv_mdsoc_capsules.md` and the implementation phase never
   landed.

2. **It is NOT merely a wrong path prefix.** A real `riscv_fpga_linux.spl` does
   exist, but under a different root — `src/lib/hardware/fpga_linux/
   riscv_fpga_linux.spl`, **1123 lines**. That is the pre-split monolith (the
   spec's overview describes splitting a 4547-line file down to a <30-line
   facade), and none of the three capsule files exist under that root either:

   ```
   src/lib/hardware/fpga_linux/__init__.spl               13
   src/lib/hardware/fpga_linux/riscv_fpga_linux.spl     1123
   src/lib/hardware/fpga_linux/soc_boot_sim.spl          157
   src/lib/hardware/fpga_linux/soc_vhdl_gen.spl           14
   src/lib/hardware/fpga_linux/synthesis_wrapper.spl     277
   src/lib/hardware/fpga_linux/xdc_gen.spl               237
   ```

   So repointing the specs at `src/lib/hardware/fpga_linux/` would not make them
   pass — this is a different defect from the stale-path family repaired in the
   same lane (`bitfield_reorder_spec.spl`, `struct_reorder_spec.spl`), where the
   target code existed and had only moved into `_TypeLayout/`/`_Attributes/`
   submodules.

3. The one dependency that *does* exist,
   `src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl`, is why
   `debug_sidecar_json_order_spec` still passes 12 of its 22 examples: only the
   10 that touch the missing capsules fail.

## Why not fixed now

Making these green means **performing the refactor**: splitting the 1123-line
`riscv_fpga_linux.spl` into an orchestrator / data / manifest capsule triple
against per-file line budgets (<900 / <2700 / <200) and reducing the original to
a re-export facade, while preserving its public API. That is the `#rtl-mdsoc-reorg`
phase-3 work item itself, not a test repair — and the specs additionally encode
a *root* (`src/hardware/` vs the actual `src/lib/hardware/`) that has to be
decided before any file is written, or the split will land in a third location.

Sequenced follow-ups:
1. Decide the destination root — `src/hardware/fpga_linux/` (what the specs
   assert) or `src/lib/hardware/fpga_linux/` (where the code lives today) — and
   correct whichever side is wrong.
2. Execute the SA-3 split against that decision.
3. Only then do the `debug_sidecar_json_order_spec` key-order assertions become
   meaningful; today its `check_msg` guard is the only thing keeping the failure
   readable.
