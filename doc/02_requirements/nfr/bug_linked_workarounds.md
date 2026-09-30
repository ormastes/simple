# Bug-linked workaround nonfunctional requirements

| ID | Target | Verification mechanism |
|---|---|---|
| NFR-001 | Bug checks perform zero source-tree walks, zero source-content reads, and zero Git subprocesses for workaround discovery. | Review query call graph and test a prebuilt index independent of source contents. |
| NFR-002 | A parent build performs at most one changed-path collection and one successful index publication; workers perform none. | Build entry review and update-result counters. |
| NFR-003 | Incremental source reads are bounded by changed/untracked and previously linked paths; only explicit fullscan enumerates tracked candidates. | Changed-path fixture with unrelated files; deleted/reverted annotations removed. |
| NFR-004 | Lock, reload, validate, and atomic publication protect concurrent updates; failed batches retain prior valid bytes. | Contention/corruption fixture; inspect atomic writer ownership. |
| NFR-005 | Cache reuse remains bound to phase, producer, entry, source/dependency identity, ABI, and build options. | Bootstrap policy review; no cache stamp edits or invalidation side effects in annotation indexing. |
| NFR-006 | New app leaves use app I/O/env/process facades. Any runtime host-operation changes use the existing SOSIX owner and are audited. | Direct-env guard and scoped import/extern audit. |

Measure warm check latency on a realistic bug/index fixture and record the
sample size and elapsed time in verification evidence. Compare matched baseline
and candidate runs before asserting a speedup. A configured cache alone is not
performance evidence; use actual reuse/rebuild counters.
