# Windows frontend shard fanout ignored the enclosing memory budget

The self-hosted LLVM Hello compilation launched 43 processes with 40 requested
workers, then exceeded its enforced 5,859,375 KiB process-tree cap. Its RSS
receipt recorded 5,976,076 KiB before exit 88 and successful cleanup. The
interpreter diagnostic independently exceeded the same cap. These are memory
admission failures, not evidence that LLVM code emission failed.

`shard_mem_available_kb` only invoked awk on `/proc/meminfo`. Windows therefore
returned unknown memory; `shard_threads_cap_for` interpreted unknown as permission
to keep all requested workers. Moreover, the hermetic bootstrap environment
discarded the enclosing watchdog budget, so even a correct Windows host-memory
query would have missed the much smaller process-tree cap.

The repair uses the existing Windows memory owner under a Windows-only import;
POSIX keeps its existing probe. Shard admission uses the smaller allowance from
host headroom and a known enclosing tree budget, reserving 40% for the parent,
other owners and headroom. A 68,000,000 KiB host with a 5,859,375 KiB tree cap
admits two 1,650,000 KiB parse workers and selects the sequential path for
3,000,000 KiB HIR workers. Backend `--threads 40` remains unchanged. Unknown
host memory or an absent required Windows tree budget selects the existing
sequential path. An explicit host-clamp opt-out still respects a known tree cap.

The bootstrap wrapper derives the child's reserved explicit budget from the
same validated cap passed to its RSS watchdog, before freezing the transcript.
The fixed host-environment schema remains unchanged. Monitor-only mode records
zero rather than pretending that a cap is enforced. Caller overrides, including
mixed-case Windows aliases, are rejected. This value is a scheduling hint; the
watchdog remains the enforcement authority.

The first focused native run exposed another concrete defect: the existing
runtime conversion did not reject the decimal value 9223372036854775808.
Memory and worker-budget parsing now validates decimal digits and the i64
maximum before conversion. Inputs longer than 19 digits, including excessive
leading zeros, conservatively become unknown. The 60% arithmetic divides
before multiplication to avoid overflow.

Validation used two bounded native cycles. Cycle 1 exited 44 at the overflowing
decimal oracle. Cycle 2 compiled 31 fresh modules, zero cached or failed, then
passed 21 real oracles including the live Windows memory-owner call (75,281,852
KiB observed headroom). Its idle predecessor cache was cloned privately; actual
compiler reuse was zero. The executable SHA-256 remained
`1b41a36da7f65c1a61ebd1e4b92d5319e1ebe89f1acb2c66f6c7584cf492a309`.
The 65-byte runtime log SHA-256 is
`fe8c8bef8a5ff6ff07e7e66af2f822c5ac38589122ea373d833dcfb72a8eee94`;
the 5,399,834-byte outer log SHA-256 is
`25b76402359d7ec91c706adbc41ccdd9dd876222e5b031cec141d11fb2f732d4`.
Both match their bounded receipts. Native build, executable and outer collector
exited zero. RSS monitoring completed, peak 1,282,572 KiB, quiescent=1,
observer_errors=0. The outer collector applied residual-job cleanup; independent
inspection found no remaining processes in the lane.

Evidence: `C:/Users/user/.simple/worktrees/simple-windows-phase2/build/native_probe/windows-shard-memory-regression2`.
These are F177 bootstrap/CoreC diagnostics, not admission of a self-hosted
producer. The checked-in SSpec suite and a complete compiler rebuild remain
pending; non-Windows conditional compilation was source-reviewed, not executed.

Nine distinct transport checks passed using real hermetic child processes and
the real Windows watchdog: enforced child/transcript/receipt budget agreement,
monitor-only zero budget, five invalid caps rejected before transcript creation,
and uppercase/mixed-case override rejection. The enforced check passed in
`windows-shard-budget-transport2`; the remaining seven passed in
`windows-shard-budget-transport3`; its separate mixed-case check passed once.
Earlier harness failures (missing setup variable, then wrong monitor-mode name)
are retained. Already-passing criteria were not replayed. The full nine-case
test script has not been run as a single invocation.

Full compiler/core/MCP checks, successful rebuilt-compiler Hello execution and
Phase 2 qualification remain pending. This change establishes admission logic
and transport behavior, not completion of the backend build/test task.
