# Per-file lane (default Stage 3 route) fails before any real HIR: unit child's MIR gate wants HIR for the whole inventory

- Status: open
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
