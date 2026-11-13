# Per-file lane (default Stage 3 route) fails before any real HIR: unit child's MIR gate wants HIR for the whole inventory

- Status: fix-implemented (layer 1, 2026-11-13); default route still blocked by layers 2-3 below
- Severity: P1 (blocks the DEFAULT Stage 3 route; workaround exists)
- Found: 2026-11-12 (early Phase 3 census lane)
- Component: compiler driver, per-file unit pipeline
  (`SIMPLE_FILE_WORKERS` unset => `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"`,
  `src/compiler/80.driver/driver_build/native_file_worker_v1.spl:55`)
- Binary: run 15 admitted Stage 2, sha256 `43d4627b7d555758…`
  (`build/bootstrap-fable-15/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
  source `bfe789dd411`, aarch64, cranelift)

## Observation

### A. Stage 3 shape (bootstrap_main closure, 1623 modules)

Exact Stage 3 argv and env (`bootstrap-from-scratch.sh` ~5862-5926:
`SIMPLE_BOOTSTRAP=` empty, `SIMPLE_BOOTSTRAP_STAGE3=1`, 5 `--source` roots,
`--entry-closure --mode dynload`), `--threads 4`. Took 6 min and failed with exit 1:

```
[file-worker] owner=0/2@0 unit exit=1 hir_claimed=1 mir_claimed=0 closure_incomplete=false orphan_picks=0
[file-worker] no MIR module verdict; per-file pool selected, no in-process fallback
error: MIR shard aggregate failure; link and artifact publication blocked
```

Both first units fail on LEAF modules that import nothing:
`src/lib/common/plugin/iface_id.spl` and `src/compiler/00.common/driver_core_modes.spl`
(`[hir-shard] done ... lowered=0 claimed=1`, terminal `FAILED`). Each of these
units also prints an impossible re-export chase. Neither file has any `use`,
and no file in `src/lib/common/plugin/` names `CompileOptions`:

```
[hir-reexport-chase-unresolved] facade=lib.common.plugin.aspect_params item=CompileOptions importer=src/lib/common/plugin/iface_id.spl
[hir-reexport-chase-unresolved] facade=compiler.common.driver_core_types item=CompileOptions importer=src/compiler/00.common/driver_core_modes.spl
```

### B. Minimal repro (3 files, under 1 min)

You need a git checkout because SCV admission requires `git ls-files`. Commit
these three files locally under `src/app/p3rp/`:

```
# aa.spl
pub fn leaf_a() -> i64:
    2
# bb.spl
pub fn leaf_b() -> i64:
    3
# main.spl
use app.p3rp.aa.{leaf_a}
use app.p3rp.bb.{leaf_b}

fn main():
    print "{leaf_a() + leaf_b()}"
```

```
<stage2> native-build --target aarch64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap --source src/app --source src/lib --entry-closure \
  --threads 2 --cache-dir <d> --mode one-binary --runtime-path <stage2-runtime-authority> \
  --entry src/app/p3rp/main.spl -o <out>
```

| variant | result |
|---|---|
| default (unset) / `SIMPLE_FILE_WORKERS=1` | rc=1, `[ERROR] MIR shard error: MIR physical ownership missing HIR for app.p3rp.main` |
| `SIMPLE_UNIT_TLDR_IMPORTS=0` | rc=1, same error |

The unit child lowers HIR only for its picked leaf (`lowered=1 claimed=1`).
Its MIR step then enters the physical-ownership block in
`src/compiler/80.driver/driver_pipeline_lowering.spl:840-861`. That block
requires `hir_modules` to contain EVERY module in `source_module_names_owner`
(the whole frozen inventory). It has no exemption for the module-scoped unit
lane (`file_worker_module_scoped_selected_v1`), so the gate cannot pass in a
unit that holds only its batch. This is the same family as
`stage2_compiler_mcp_entry_native_build_blocked_2026-11-11.md` item 1, where the
unit holds only its batch and the entry is in no unit's subset. There it fails
at the cold-HIR receipt gate. Here it fails at the MIR physical-ownership gate.

## Impact

- The Stage 3 default route cannot build bootstrap_main.
  `.claude/rules/bootstrap.md` already says "Stage 3 run of the per-file lane
  is not yet proven". This report is the first measured run.
- Workaround (no code change): run Stage 3 / `resume-stage3-from-admitted.sh`
  with `SIMPLE_FILE_WORKERS=0`. Both scripts pass the value through and hash it
  into the args receipt. Verified: with FW=0 the Stage 3 capsule takes the
  `[capsule-shard] hir shards=N` route and HIR proceeds normally.

## Secondary finding (FW=0, non-capsule coordinator, `--threads >= 2`)

The plain `native-build` coordinator's HIR worker profile
(`src/app/cli/worker_hir_profile_v1.spl:21-61, 64-91`) rejects:
- the `--mode` flag: `unsupported HIR worker option: --mode`
- any environment key outside its literal list, including `SIMPLE_FILE_WORKERS`
  itself and `RUST_LOG`: `unsupported HIR worker environment key: SIMPLE_FILE_WORKERS`

So `SIMPLE_FILE_WORKERS=0 native-build ... --threads 2` fails for every
non-capsule build whose host bound allows 2 or more shard threads. The Stage 3
capsule is not affected. Run 13's `test_runner_build` passed only because its
shard threads resolved to 1 (in-process). A Phase 4 / phase C tool build at
`--threads >= 2` hits this.

## Fix direction

1. The per-file unit's MIR step must scope physical ownership to the unit's
   admitted targets (the module-scoped MIR shard path), not the whole inventory.
   Then re-prove the default lane on the 3-file repro before relying on it for
   Stage 3.
2. Explain the leaf-unit `CompileOptions` chase. A leaf with no imports must not
   register any re-export chase. Suspect surfaces registered from the wrong
   module (TLDR surface registration) or a Stage 2 miscompile.
3. HIR worker profile: admit `--mode <v>`. Decide the environment policy for
   inherited knobs (`SIMPLE_FILE_WORKERS`, `RUST_LOG`, ...). Either admit them
   or strip them before the child spawn. Do not let them fail the build.

## 2026-11-13: layer 1 fixed, two further layers found

Fix (branch `work/stage3-per-file-route-fix-20261113`): in a module-scoped
unit (`worker_hir_loads_restricted_v1()`), both MIR ownership gates
(physical inventory, and the checked entry-alias projection taken under
`SIMPLE_BOOTSTRAP=1`) keep an unheld NON-target row as a placeholder
(`driver_mir_owner_disposition_v1`, like a go-to-end exclusion). An unheld
target still fails closed; outside a scoped unit nothing changes. The MIR
ledger schedule names unheld rows by their canonical logical module
(`driver_mir_schedule_name_v1`) so every unit publishes the same must-match
inventory, and the only-paths skip now runs before the per-row HIR name read.
Spec: `test/01_unit/compiler/driver/mir_physical_owners_spec.spl` (seed, red
14/20 -> green 20/20).

Native evidence: a Stage 2 built from the fix worktree by run 20's pinned
seed (1638 files, 790 s). 3-file repro, default route: both leaf units now
run HIR -> MIR -> object (`[mir-shard] done ... claimed=1 passed=1`); the
"MIR physical ownership missing HIR" error is gone on both `SIMPLE_BOOTSTRAP`
settings. Run 20's own Stage 2 still shows the original error, because its
binary predates the fix.

The first IMPORTING unit (`main`) still fails, differently per TLDR setting:

- Layer 2 (default, unit TLDR imports on):
  `FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing for <snapshot>/src/app/p3rp/main.spl`.
  `SIMPLE_COMPILER_PHASE_PROFILE=1` shows
  `phase2:surface:missing-direct-edge ... source=<scv snapshot>/src/app/p3rp/main.spl target=<checkout>/app/p3rp/aa.spl`.
  main's import edges point at surface rows whose canonical path is
  `<checkout root>/app/p3rp/aa.spl`, which has no `src/` and no SCV snapshot
  prefix. They do not point at the summary-built surfaces registered under the
  snapshot path, so `surface_built` is false for both imports.
- Layer 3 (`SIMPLE_UNIT_TLDR_IMPORTS=0`): the closure loads (`modules=3 of=3`).
  Phase 3 then fails `HIR completion receipt publication failed`
  (`driver_hir_pipeline_lowering.spl` ~1496) right after `aa` loads from the
  cache. Suspect: an unclaimed import that missed the cache is lowered
  in-process, and the unconditional `hir_shard_finish(path, "PASS")` is then
  refused because another unit already owns that row.

Also observed: under a 12G cgroup the pool refuses ("need >= 2", 9 GB per
worker). `file_worker_pool_refusal_v1` does not apply the guarded >= 2 floor
(`shard_threads_guarded_floor_v1`). The probes needed
`SIMPLE_{HIR,MIR}_SHARD_WORKER_KB=2000000`.

Review follow-ups (LAND-WITH-NITS, both fail closed today):
- Entry-closure alias rows (`driver_source_pipeline_loading.spl:1253`, which
  takes `module_name` from the import spelling) are probably the next
  blocker. In a unit that does not hold the file, the placeholder
  `canonical(logical)` differs from the path-derived `HirModule.name` that
  another unit uses. The result is "conflicting owners" or a ledger
  row-count refusal. Candidate fix: name the placeholder by the path-derived
  module name.
- Placeholders are safe only because the only-paths skip runs, and that skip
  requires an active MIR shard queue. Tie the disposition to the queue being
  active.
