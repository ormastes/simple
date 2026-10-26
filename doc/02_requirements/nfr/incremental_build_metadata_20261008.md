# Incremental build metadata nonfunctional requirements

<!-- codex-design -->

Status: targets for qualification, not measured results. User-selected goal: fast pure-Simple compilation with verified TLDR reuse, preserving memory and logic correctness. Derived scope and optional defaults follow the supplied research; no optional source commit or remote publication is enabled.

| ID | Requirement | Verification |
| --- | --- | --- |
| NFR-IM-001 | <=100 ms p95 representative warm changed-entry SPL-to-object, including standalone startup/admission; one new object, zero imported-body codegen | Exact fixture and bounded sample matrix in system-test plan; cold/link/service startup reported separately |
| NFR-IM-002 | Warm unchanged admitted input causes zero source-body parse/lower/object emission | Production phase and process-tree counters, not file-existence guesses |
| NFR-IM-003 | No mandatory Git/SCV/runner/daemon process for standalone compile | Disable services and inspect actual child processes while compiling/running |
| NFR-IM-004 | No stale semantic reuse, false verified receipt or pending-to-pass conversion | Fresh/reused differential tests, negative witnesses, formal model and failure injection |
| NFR-IM-005 | Bounded metadata, queues, waiters and reader lifetimes; no whole-artifact copies solely for hashing/header inspection. Bounded decoded headers may be shared once per pinned generation | Memory-pressure/cancellation/GC tests, private commit/RSS and retained-byte counters |
| NFR-IM-006 | Parallel useful work scales within shared host resources without same-key duplicate publication or waiter deadlock | 1/4/20/40/80 concurrency plus 128 logical-task scheduler tests |
| NFR-IM-007 | Post-binary durable enqueue targets <=10 ms p95 local SSD without mandatory SCM writes | Isolated enqueue measurement; target adjusted only with evidence |
| NFR-IM-008 | Errors identify actual stage, source/producer/key and cache miss reason with bounded logs | Corrupt input, crash and degraded-span fixtures; module progress is not final artifact qualification |
| NFR-IM-009 | Standalone fallback and packed SMF compatibility remain correct | Missing metadata/daemon/CAS and pack/unpack/link/runtime parity matrix |

Compare baseline and candidate on identical input, compiler/toolchain configuration and cache state. Preserve previously passing evidence unless a relevant change invalidates it. A faster but incorrect or unbounded-memory result fails. Targets are not universal promises for arbitrary module size, CTFE work, optimization or cold environments.
