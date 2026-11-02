# Stage 3 bootstrap-fixed closure MIR lowering retains ~36 MB per module

- Status: FIX-IMPLEMENTED-VERIFICATION-PENDING (2026-11-02)
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Blocks: Stage 3 MIR phase after the closure-loop SIGSEGV fix (83ff46b0bc4).

## Observation

Diagnostic Stage 3 (provisional: Stage 2 relinked from r14's cache with
83ff46b0bc4, sha256 `ce8bd78f...1fed`; sharded route, 8 HIR workers all
completed, 0 failed). After `phase4:monomorphize:done` (+1394859 ms) the
bootstrap-fixed lane lowered 1100 closure modules
(`aot:bootstrap_fixed:closure_module`) in ~96 s while the compiler grew:

| time | RSS | phase |
|---|---|---|
| 23:58:47 | 13.2 GB | monomorphize start |
| 23:59:48 | 18.4 GB | monomorphize |
| 00:00:49 | 30.7 GB | MIR closure modules |
| 00:01:49 | 52.9 GB | MIR closure modules (~1100 done) |

then the run received SIGTERM at 00:02:50 (external). ~36 MB retained per
closure module. The loop (`driver_pipeline_lowering.spl:938-951`) lowers
every module on one `MirLowering` instance with `lower_module` and no
transient scope, unlike the direct lane's `lower_module_transient_scoped`
(`module_lowering.spl:2070`), which promotes only the returned MirModule.

The SIGSEGV this lane was fixing is gone: closure modules lower normally.

Revalidated 2026-11-02: still plausible because Status is still OPEN and no fix for the per-module MIR retention is referenced or found.

## Fix status (2026-11-02)

Root cause: the closure loop lowered every module on one shared `MirLowering`
with plain `lower_module`, so each module's lowering arena (sidecars, block and
instruction graphs, diagnostic text) was never reclaimed.

Fix (in source, 75b8426be39 and 2758c8344d7): `driver_pipeline_lowering.spl:1055`
calls `lower_bootstrap_closure_module`
(`_MirLowering/module_lowering.spl:2299`), which goes through
`lower_module_transient_scoped(module, providers, false)`. Only the returned
MirModule, the owner inventory and the `_bootstrap_mir_*`/`_bootstrap_fn_*`
registries are promoted. Consumer-local tables are cleared for non-entry modules.
A refused scope logs `[mir-scope] WARNING transient scope refused`, then lowers
unscoped.

Evidence (Windows, `bin/simple test`): `bootstrap_fixed_closure_scoped_lowering_spec`
6/6 (54 s, peak 192 MB); `bootstrap_closure_provider_retention_spec` 5/5
(156 s, peak 192 MB). These are source-contract specs only. The retention
symptom reproduces only on a full Stage 3 run.

Repro steps to close:
1. Run the stage3 bootstrap-fixed lane (`scripts/bootstrap/bootstrap-from-scratch.sh`,
   Stage 3) with `SIMPLE_BOOTSTRAP=1` on a stage2 that includes 2758c8344d7.
2. Sample compiler RSS each minute from `phase4:monomorphize:done` through
   `aot:bootstrap_fixed:done`.
3. Pass: the ~1100 `aot:bootstrap_fixed:closure_module` lines add << 36 MB per
   module (old run: 13.2 -> 52.9 GB), and there is no `transient scope refused` warning.
