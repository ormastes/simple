# native-build stall pattern (mcp closure, aarch64 host, 2026-09-25)

Four attempts to native-build the simple_mcp_server closure (2026-09-24/25), zero completions:
1. Clean-worktree pair: died silently at 'execute main start' (~2h).
2. Replacement pair: 6h parked (all threads futex-wait, RSS 13.7GB, CPU plateau).
3. Main-worktree build: died silently ~12 min in (log tail = collision warnings, no error, no EXIT).
4. Main-worktree rebuild: 4h54m wall; CPU time FROZE at 03:46:12 (~6s of CPU in the final 3.5h) — parked threads, RSS 360MB, zero output.

Pattern: the build reaches a post-codegen phase ('[rust-jit] execute main' / link) and its threads park on futexes permanently. No error, no EXIT line, no output binary. The other-lane reroot closure (pid 488914) DID finish in 52 min on the same host/binary, so this is closure- or phase-specific, not universal.

Working alternatives verified meanwhile: interpreter mode (bin/simple run src/app/mcp/main.spl) passes initialize + stdio specs; deployed Sep-6 native binaries answer --version + initialize but fail the wrapper's strict native probe.

Next compiler-lane action: attach a debugger to the parked phase (gdb -p on a fresh stall, thread apply all bt) to find the futex owner; suspect the JIT-execute/link driver lock or the SCV snapshot walk deadlock.
