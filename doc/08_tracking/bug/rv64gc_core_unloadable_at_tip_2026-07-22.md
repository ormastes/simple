# rv64gc_rtl/core.spl unloadable at origin tip (3 stacked defects)

**Filed:** 2026-07-22 (lane W2-D, verified at origin tip during soc_top_64 wiring)
**Status:** FIXED (lane A, 2026-07-22) — (1) `@hardware` removed, matching the
decorator-free rv32i_rtl/core.spl pattern. (2) Clocked `core64_cycle`/phased-
memory path and PMP state REMOVED pending re-land together with real
`memory_access`/`pmp`/`pmp_csr` modules (removal route; no speculative
modules; deferred re-land tracked here). (3) `is_csr`/`csr_addr` added to
`DecodeResult64`, populated in decode (SYSTEM opcode, f3&0x3!=0;
insn[31:20]). Gate: in-tree `bin/simple run` core64_probe + soc_top_64_probe
ALL PASS; rv32 probe regression-clean. SSpec runner still blocked by the
deployed-seed runner defect (separate bug).
**Severity:** blocker for any in-tree execution of the RV64 core path

`bin/simple run` on ANY importer of `std.hardware.rv64gc_rtl.core` fails. Three
independent defects, identical pre/post the W2-D change (baseline-verified):

1. **Unknown `@hardware` decorator** — `error: semantic: variable 'hardware' not
   found`. core.spl is the only file in the tree using `@hardware`; the known
   decorator set is @allow/@tag/@no_gc/@gc/@inline. Either register the
   decorator or remove it.
2. **Missing modules** — `core64_cycle`/`core64_init`/`core64_reset` call
   `memory64_start`/`memory64_cycle` from `std.hardware.rv64gc_rtl.memory_access`
   and use `pmp`/`pmp_csr` (`PmpEntries64`), but no `memory_access*`, `pmp*`
   files exist anywhere in the tree. The July-18-lineage reland (81d904de4b5)
   brought the callers without these dependency modules.
3. **core/decode field mismatch** — core.spl reads `dec.is_csr`/`dec.csr_addr`;
   `DecodeResult64` defines neither field.

**Impact:** `core64_cycle` (bus-protocol path) cannot execute; W2-D therefore
wired `soc_top_64_tick` through `core64_combinational`+`core64_update` (whose
dependencies all exist). SSpec gates for soc/core64 cannot run until fixed
(also masked by the deployed-seed runner hang, see
`deployed_seed_test_runner_init_hang_2026-07-17.md`).

**Repro:** `bin/simple run` any file with `use std.hardware.rv64gc_rtl.core.{core64_init}`.

**Mechanical-removal reference diff** (shadow-harness fix used to obtain W2-D
gate evidence; removals only, for whichever lane owns core.spl repair):
session scratchpad `w2d_core_prebroken_fix_reference.diff` (385 lines).
