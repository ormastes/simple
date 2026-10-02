# Windows Cranelift Phase2 build with 80 workers: timeout failure

**Status: FAIL.** No Phase2 compiler or downstream native test executables were produced. The tested source was frozen release commit `1ffaf797bab1b6747d4e24856ed6c1af990e178e`, with the evidenced MSVC LLVM 23.1.1 toolchain. The build requested 80 workers on a host reporting 64 CPUs, using explicit-count authority and `SIMPLE_NO_STUB_FALLBACK=1`.

## Authoritative results

The additional authorized attempt, session `96437`, terminated with exit 1. Its Windows bounded-process receipt records `reason=child-exit` and `native_exit_status=1`. The independent 7,200-second whole-process deadline did not cause the failure.

The native build reported `compiled=995 reused=0 failed=123` across 1,118 source entries. All 123 failure rows report `timeout (300s)`; none report another failure type. The failures comprise 101 compiler files, 14 library files, and 8 application files. The private Stage2 native cache retains 995 object files. Because `bootstrap_main.spl` also timed out, no Phase2 compiler was emitted; full CLI, test runner, and native interpreter, loader, and compiler qualification remain **BLOCKED**. No retry was launched.

The [complete failed-file metadata](windows_cranelift_phase2_timeout_files_2026-10-02.json) records all 123 paths, their source sizes, and their groups. Retained process evidence is under `C:/Users/user/.simple/worktrees/simple-windows-phase2/evidence/cranelift-attempt4/`: `producer.log` and `producer.receipt.env`. The native build log is `build/bootstrap-cranelift80/logs/x86_64-pc-windows-msvc/stage2-native-build.log` under the same worktree storage root.

## Timeout mechanism

The bootstrap-only Rust compiler's `compiler/src/pipeline/native_project/compiler.rs` dispatches regular Rayon jobs to `compile_file_safe` after their queue slot begins. That function spawns a compiler thread; `wait_for_compiler_thread` uses `recv_timeout` with a wall-clock duration. Queue waiting before dispatch is excluded. Scheduling contention, import resolution, and code generation after the compiler thread is spawned count toward the 300-second timeout. Per-thread CPU and phase timing were not measured in this attempt.

On timeout, the join handle is dropped without joining or cancelling its worker. That detached worker can continue while Rayon admits more work, potentially increasing concurrency beyond the requested pool after timeout waves. The same source already documents facade starvation in a 32-worker build and compiles recognized contention-sensitive entries sequentially before broad fanout.

Failed input sizes range from the 268-byte `driver_hir_pipeline_impl.spl` to the 247,992-byte generated `hir_codec.spl`. Source byte size alone does not explain or adequately budget this workload.

## Follow-up and cache preservation

Existing `SIMPLE_NATIVE_FILE_TIMEOUT` configuration and canonical Stage2 `--timeout` forwarding support a larger finite diagnostic budget. A new configuration owner is unnecessary. The [reviewable retry proposal](windows_cranelift_phase2_timeout_retry_proposal_2026-10-02.md) specifies 1,200 seconds per file under the existing 7,200-second whole-process bound. Its execution requires fresh user authorization because the additional Cranelift attempt was consumed.

Preserve the 995 completed objects and retained frontend/HIR records. Any later compatible incremental attempt must report actual reuse and rebuild counts. Directory existence does not establish a cache hit. Further performance work should record queue dispatch, compiler-thread start and completion, phase timings, CPU metrics, and detached workers; it must preserve source/runtime identity, persistence, and the prohibition on unresolved stubs. This diagnostic made no product or seed source edits.
