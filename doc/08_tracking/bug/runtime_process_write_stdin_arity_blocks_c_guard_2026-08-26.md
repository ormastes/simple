# Runtime process write-stdin arity blocks the C runtime guard

**Status:** OPEN  
**Observed:** 2026-08-26

`sh scripts/check/check-c-runtime-compiles-push.shs` fails in
`src/runtime/runtime_process.c:1736` because `rt_editor_start_simple_dap` calls
`rt_process_write_stdin(pid, text)` while the current declaration requires four
arguments.  The same failure propagates into two browser-renderer selfcheck
translation units that include this owner.

This is independent of the TCP/UDP SFFI ABI work.  It prevents the whole-tree C
guard from proving the runtime even though a focused `_GNU_SOURCE` syntax check
of the touched `runtime_native.c` succeeds.  Fix by routing both DAP frames
through the canonical length/status contract and add a focused process-runtime
test; do not add a compatibility default or fabricate success.
