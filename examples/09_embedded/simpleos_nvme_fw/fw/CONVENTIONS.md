# NVMe firmware (`fw/`) — coding conventions

Host-runnable **simulation** of a bare-metal NVMe SSD firmware, layered HIL → FTL → FIL.
Written in pure Simple. These conventions exist to work *with* two confirmed self-hosted
compiler bugs while keeping the code production-shaped.

## Module layout
- **MDSOC everywhere; the ECS business layer is scoped *per dimension*, not per artifact.**
  Domains layer strictly downward (HIL → FTL → FIL; every cross-domain import points down),
  composition over inheritance, no shared mutable global. CLAUDE.md's rule — "MDSOC outer + ECS
  business layer for userland services/apps; kernel/drivers stay MDSOC-only" — is applied to each
  dimension separately, because an SSD spans both classes:
  - **HOST** (`hil*`, `nvme_*`, `fw_pool`, `dram`, `power_thermal`, `openssd_config`) and
    **FTL** (`ftl*`, `rain`, `rel_*`, `hooks`, `sandbox`) are **service-class**. Target:
    **MDSOC+ = MDSOC outer + ECS inner**. `use std.ecs` is *permitted* here.
  - **NAND/FIL** (`fil*`, `nd_types`) is **driver-class**: **MDSOC-only**, and `use std.ecs`
    stays **forbidden** — "drivers are IO-bound state machines, not entity graphs"
    (`doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md` Layer Rules).
  - `nvme_types` is the shared frozen interface; `firmware.spl` is the composition root and is
    the only module allowed to name more than one dimension. The 4 harness modules
    (`sim_main`, `test_fw`, `fw_layer_smoke`, `nand_migration_capture_main`) are harness-tier,
    outside all dimensions. Each `*_check.spl` takes its subject module's dimension.
- **Current state: pre-migration.** No ECS exists in this tree yet — `grep -r "use std.ecs" fw/`
  still returns nothing, and every module is plain MDSOC today. The bullet above states the
  **target** rule that the migration is executed against, not what is built. Controlling plan:
  `doc/03_plan/hardware/nvme_mdsoc_plus_layer_architecture.md` (phases 0-8); spine
  `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md` §3. Ownership of the
  `rel_*` reliability group (FTL policy vs NAND-owned retry ladder) is an **open question**,
  decided before Phase 3 — see that plan's S5.
- Downward-only layering is gated by `scripts/check/check-nvme-layer-dependencies.shs`, which
  parses the `use` graph of `fw/*.spl` and ratchets against the known pre-migration offenders.
- All modules are flat in `fw/`; the frozen shared interface is `nvme_types.spl`.
- Import siblings with the **bare** form: `use nvme_types.*`, `use fil_nand.*`, … (the
  package-qualified form `use simpleos_nvme_fw.fw.X.*` emits an E1034 resolution warning).
- A module **must not** contain `fn main()` (importing two mains collides — last-write-wins).
  Each module exposes `fn <module>_selftest() -> i64` returning a failure count (0 = pass),
  built from `expect_eq` (in `nvme_types`).

## The verification gate is `bin/simple run`, not `check`
`bin/simple check` has a non-deterministic **typecheck-blowup** that hangs/crashes on
array-field structs with several `me` methods (bug:
`doc/08_tracking/bug/sspec_simple_check_superlinear_two_impls_2026-06-29.md`). The
interpreter is unaffected, so every module is gated by running its self-test:
`bin/simple run` a tiny harness that calls `<module>_selftest()` and expects `… OK` exit 0.

## The first-param ×8 interpreter bug (conditional)
A **rare, method-specific** interpreter defect: for *some* multi-param `me` methods, the
FIRST parameter binds to `value × 8` on entry. It is **not** universal (most multi-param
`me` methods are fine — `fil_nand.program`, `fw_pool.acquire`, etc. all round-trip their
first param correctly) and is not reproducible in isolation; the exact trigger is internal
to method-table layout. Confirmed live in `ftl_journal.append` only. Bug:
`doc/08_tracking/bug/interp_me_method_first_param_times8_conditional_2026-06-29.md`.

**Mitigation (mandatory):**
1. **Test every stored param.** Every multi-param `me` method's self-test must round-trip
   *each* stored value (e.g. `acquire`'s `cid` via a `cid(h)` accessor), so a ×8 corruption
   surfaces instead of lurking.
2. **If a value reads back as `value × 8`,** add a leading dummy `_p0: i64` param (callers
   pass `0`); the corrupted "first param" is then a throwaway and the real args shift to
   position 2. (Applied in `ftl_journal.append`.)
3. **Prefer the clean form for new code:** a `me` method with 2+ values should take a single
   struct param (single-param `me` methods are always unaffected) — this also satisfies the
   repo's "3+ params → struct" rule.

## Call-boundary: bind a method-call result before passing it
Never pass a **method** call's result *directly* as a method argument —
`outer.m(inner.n(...))` corrupts the inner value at the call boundary under a **nested**
interpreter (the program runs fine standalone via `bin/simple run`, but fails deterministically
when it runs as a `process_run` subprocess of `bin/simple test`). Bind it first:
`val p = band.alloc_page(); band.mark_valid(p)`. (Passing a **free-function** result —
`fw.submit(cmd_make(...))` — is fine.) Bug:
`doc/08_tracking/bug/interp_method_call_result_as_arg_corruption_nested_2026-06-30.md`.

## Generation handles
The object-pool stale-handle guard (`fw_pool`) must be tested by **re-acquiring a freed
slot** (so `used==1` again) and asserting the OLD handle is rejected via **generation
mismatch** — not merely by the `used==0` flag.
