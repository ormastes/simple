# Stage 3 bootstrap-fixed closure MIR lowering retains ~36 MB per module

- Status: OPEN
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
