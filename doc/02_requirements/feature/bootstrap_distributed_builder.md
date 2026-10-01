# Bootstrap distributed builder requirements

Date: 2026-09-30. Selected scope: the user's restart instruction and retained
bootstrap restart policy, with current clarification that cached script-driven
bootstrap proceeds concurrently and manager adoption waits for qualified compiler
and manager artifacts. These are retained instructions, not auto-selected options.

Current ordering clarification: build the native manager with the genuine
permitted Phase 1 seed and retain it through Phase 4. Grouped isolated local
workers come first; distributed execution follows separately. Worker image
identity must be explicit per host, including a separate Windows worker.

| ID | Required behavior | Completion evidence |
|---|---|---|
| REQ-BBM-001 | Immutable source snapshot, preceding producer, toolchain, task/attempt identities; bounded versioned request/result protocol | Strict malformed/truncated/oversized records rejected; changing identity rejects stale results; real input hashes checked |
| REQ-BBM-002 | Native manager compiled and sanity-tested by the permitted genuine Phase 1 producer, retained through Phase 4; adopt when required compiler and manager are ready | Producer/source/manager/per-host worker hashes and successful native launch receipts; no circular build dependency; seed used only for this authorized bootstrap construction |
| REQ-BBM-003 | Actual local and explicitly configured remote compilation workers | Owned process execution and output receipts locally and on the configured remote; protocol simulation alone is insufficient |
| REQ-BBM-004 | Worker crash isolation, kill-and-reap before replacement, bounded retry, stale-attempt rejection | Real worker crash and restart; surviving workers complete; late prior-attempt output cannot publish |
| REQ-BBM-005 | Completed dependencies gate dispatch; independent work continues under keep-going; fail-fast selectable; every task gets a terminal row; incomplete results never link/publish | Dependency failure blocks consumers, independent success survives, aggregate exit remains nonzero, missing outputs reject clean exit |
| REQ-BBM-006 | Phase/producer/task isolated writable caches, verified reuse, narrow invalidation | Unchanged task reuses rehashed result; changed input/producer/toolchain invalidates only dependent work; old cache retained; unobserved compiler cache counters remain unknown |
| REQ-BBM-007 | Compiler emits real module/SCC work through the manager | Native compiler invocation reaches worker processes and admits their objects; codegen coverage distinguished from parsing/HIR/MIR and whole-binary tasks |
| REQ-BBM-008 | Bootstrap scripts, checker, SPipe instructions, wiki and guides describe actual workflow | Current documentation and executable/manual traceability; restart report contains source/producer/cache/process identities and unfinished gates |

Windows and Linux evidence remain separate. A missing permitted host or producer
is incomplete evidence, never an accepted scope exclusion. No claim of full
bootstrap success follows from manager unit tests or manifest validation.
