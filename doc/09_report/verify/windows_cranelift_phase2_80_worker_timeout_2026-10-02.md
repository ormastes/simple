# Windows Cranelift Phase2 80-worker timeout failure

Status: FAIL; no Phase2 compiler or downstream executable tests produced.
Source: frozen release HEAD1ffaf797bab1b6747d4e24856ed6c1af990e178e.
Tools: evidenced MSVC LLVM23.1.1. Native jobs80, host CPUs64, explicit-count authority. No stub fallback.

## Authoritative results

Additional authorized attempt session96437 terminal exit1. Windows bounded-process receipt reasonchild-exit/native_exit_status1; outer deadline7200seconds was not the failure. Stage2 log reports compiled995, reused0, failed123 over1118source entries;995object files remain in private stage2-native-cache. All123failure rows are timeout300s; no non-timeout failure rows. Groups: compiler101,lib14,app8. Failed bootstrap_main.spl prevented compiler output, so full CLI/test runner/native interpreter-loader-compiler qualification remained BLOCKED. No retry was launched.

Paths: C:/Users/user/.simple/worktrees/simple-windows-phase2/evidence/cranelift-attempt4/{producer.log,producer.receipt.env}; build/bootstrap-cranelift80/logs/x86_64-pc-windows-msvc/stage2-native-build.log. Complete123file size/group metadata: runtime/cranelift80-timeout-file-metadata.json.

## Exact timeout mechanism

Rust bootstrap-only compiler/src/pipeline/native_project/compiler.rs regular Rayon jobs call compile_file_safe after their queue slot starts(lines479-487). compile_file_safe1038spawns a compiler thread; wait_for_compiler_thread1137uses recv_timeout with wall duration, not CPU time. Therefore pre-dispatch Rayon queue wait is excluded; scheduling starvation and import resolution/codegen after thread spawn count toward300seconds. On timeout the JoinHandle drops without joining/cancellation; that detached worker can continue while Rayon admits further work. This can exceed intended concurrency after timeout waves. No evidence here establishes per-thread CPU contribution or the fraction spent resolving imports.

The source already documents facade starvation at32workers and sequentially admits recognized contention-sensitive entries before broad fanout(lines460-477). Failure spans268byte driver_hir_pipeline_impl.spl through247992byte generated/hir_codec.spl, so input byte size alone is not a useful budget.

## Follow-up and cache policy

Existing SIMPLE_NATIVE_FILE_TIMEOUT config and canonical Stage2 --timeout forwarding support a finite larger diagnostic budget; no new configuration owner is needed. Root plans LLVM1200seconds per-file under existing7200seconds overall. Cranelift retry requires explicit additional authorization because its granted attempt is consumed. Preserve995completed objects and all failed frontend/HIR records; a later compatible incremental attempt must report actual reused/rebuilt counts, not infer hits from directory presence.

Suggested runtime investigation: record queue dispatch, actual compiler-thread start/completion, phase timing and CPU metrics; measure detached timed-out workers; make timeout cancellation/concurrency policy explicit without silently permitting unresolved stubs, disabling persistence, or weakening source/runtime identity. No product/seed source edits or unbounded retry made in this diagnostic.