# Phase 2 test runner facade omission and post-HIR crash

The full direct LLVM matrix rejected db_test_info_lookup when lowering the test runner: the synchronous provider defines it, but the asynchronous facade omitted its explicit re-export. Add the helper to the facade list without changing behavior.

The canonical isolated LLVM command (native-build src/app/test_runner_new/main.spl --backend=llvm --low-memory --threads 1) with the corrected facade completed HIR: 667/667 modules, zero failed, 667 stores. It then crashed with exit 139 before producing the binary. Thus the missing-export blocker is cleared, but full build qualification is FAIL. Peak process-tree RSS was 2134344 KiB, below the 5859375 KiB cap, and quiescent=1. This is not the prior concurrent-matrix RSS-cap failure.

Evidence: /tmp/simple-database-export-repair/runner-canonical.log and runner-canonical.rss.env. A bounded gdb reproduction is running via crash-debug.shs; gdb.log retains diagnostics. No core file was available. The compiler hash is 5753f2a05d858132882a354916ba6f4497948174297f4f318092734ab528a7af. Test-runner execution, complete Phase 2, later phases and RC qualification remain blocked by the crash.
