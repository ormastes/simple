# method_calls_literals.spl exceeds fixed 300s native file timeout

READY FOR OPUS REVIEW. Severity P2 (perf, first-object-in-10s rule violated). Status: open.

Repro: stage2 native-build (command above, without --timeout) compiles every file but src/.../method_calls_literals.spl times out at 300s (DEFAULT_NATIVE_FILE_TIMEOUT_SECS, no CLI knob in older seeds); reproduced twice (stage2 #5, #6), 184 files NOT_ATTEMPTED afterward.
Workaround: --timeout 1500 in run4.ps1 (compiled 188 ok). Needed: profile that file (superlinear codegen) and fix, or record per-file cost.
