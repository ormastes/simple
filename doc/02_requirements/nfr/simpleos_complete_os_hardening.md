# SimpleOS Complete OS Hardening — Non-Functional Requirements

Status: **Selected** (2026-08-20)

## Selection record

The user selected the strongest robustness, safety, completeness, ownership, reproducibility, and performance profiles:

- `NFR-1B`: QEMU plus physical/native evidence on all three architectures.
- `NFR-2B`: strict interactive/server/storage/toolchain performance budgets.
- `NFR-3A`: mission-critical robustness and security depth.
- `NFR-4C`: static core bounds plus configured application budgets.
- `NFR-5A`: one canonical owner and zero unexplained subsystem duplicates.
- `NFR-6A`: controlled repeated performance measurements.

## Required targets

### NFR-001 — Architecture evidence

Every x86_64, AArch64, and RISC-V 64 acceptance row shall have a fresh nonce-bound QEMU system receipt and an identified physical-board or native-host receipt. Evidence records target triple, firmware/boot/download path, accelerator/emulator, board/CPU identity, binary/image hashes, executed argv, ordered serial/SSH/visual artifacts, exit status, owner, and independent reviewer. QEMU proves only its classified execution mode; physical rows cannot be inferred from QEMU.

### NFR-002 — Strict performance budgets

On applicable native/current-host profiles:

| Workload | Required budget |
|---|---:|
| Warm server startup p95 | <= 125 ms |
| HTTP/DB loopback request p95 | <= 5 ms |
| SSH session establishment p95 | <= 125 ms |
| WM first themed frame | <= 250 ms |
| WM input-to-present p95 | <= 25 ms |
| WM steady frame p99 at 60 Hz | <= 16.7 ms |
| Filesystem metadata operation p95 | <= 2.5 ms |
| Filesystem sequential throughput | >= 100 MiB/s |
| Guest Simple hello compile+run | <= 2.5 s |
| Guest C/C++ hello compile+link+run | <= 2.5 s |

Comparable regressions fail above 5% for latency, RSS, throughput, or FPS. Explicit QEMU TCG samples are correctness/tendency evidence only and cannot satisfy native timing targets.

### NFR-003 — Reproducible measurement

Every performance gate shall use a fixed realistic fixture/configuration, warmup, at least ten measured repetitions, raw samples, p50/p95/p99/max and max RSS where applicable, binary/image/config hashes, CPU/frequency/accelerator/noise metadata, and coefficient of variation <= 5%. Non-comparable or noisy campaigns are `BLOCKED`, not PASS.

### NFR-004 — Mission-critical robustness

Release requires zero unresolved critical/high security, data-loss, memory-safety, unbounded-resource, false-success, or authentication-bypass defects. Each parser/media family shall pass at least 1,000,000 deterministic fuzz/property cases and targeted malformed/corruption matrices. Servers, filesystems, loaders, tools, and WM shall complete a 24-hour lifecycle/soak campaign with bounded receipts.

### NFR-005 — Static core and dynamic application bounds

Kernel, filesystem, loader, network framing, credential, and evidence ingress paths shall use statically enforced size/count/time bounds. Servers, compiler processes, utilities, and WM shall use configured runtime quotas. A 1,000-cycle start/stop/cancel/restart campaign shall return handles, tasks, queues, retained bytes, and RSS to within 5% of steady baseline with zero leaked owned resources.

### NFR-006 — Authenticated execution safety

Executable manifests and privileged system payloads shall be authenticated by a versioned trust root with revocation and recovery procedures. Hash verification alone is integrity evidence, not signer or placement authentication. Verification shall bind the open handle used for loading, and trust/policy decisions shall not race pathname replacement.

### NFR-007 — Parallel ownership safety

Every mutable root and execution domain shall name its owner. Boundary data shall be copy, frozen share, owned move, scoped loan, handle, encoded payload, or lease. Bounded mailboxes/transports, cancellation, move invalidation, deterministic parent validation/commit, generation/replay defense, and process/device isolation shall be tested. Unknown access/layout facts force conservative reference behavior and may not authorize `noalias`, transfer, or parallel scheduling.

### NFR-008 — Duplication gate

Changed pure-Simple code shall pass token duplicate checks at five lines. Any competing subsystem owner or meaningful duplicate logic fails verification unless an exception records owner, rationale, quantified correctness/performance cost, expiry, and removal plan. The selected feature permits no unexplained existing FS/loader/server-lifecycle/WM/input/render duplicates at completion.

### NFR-009 — Coverage and stub prevention

Changed production branches shall achieve at least 80% branch coverage through unit, integration, and system evidence. New or modified files shall contain no `pass_todo`, tautological assertions, silent no-op helpers, hardcoded success, commented-out implementation, empty bodies, fabricated handles/events/artifacts, or fixed-command substitutes.

### NFR-010 — Protocol/security policy

Protocol capability manifests, algorithm allowlists, credentials, keys, limits, and trust roots shall be versioned and fail closed. Secrets shall not appear in logs, test artifacts, diagnostics, core dumps, generated manuals, or persisted receipts. Credential wipe shall be compiler-resistant and independently checked.

### NFR-011 — Recovery and durability

Every promised durable transition shall name its commit point, ordering, flush/barrier behavior, recoverable states, detection method, repair/recovery action, and data-loss boundary. Power-cut/corruption campaigns shall bind image hashes and never count a mount, replay, or reboot as success when committed data was fabricated or silently lost.

### NFR-012 — Evidence freshness

Only receipts produced after the last relevant source/config/artifact change may satisfy a row. Static reports, source scans, self-tests, staged files, old PASS markers, host-side execution, `SKIP`, and missing-prerequisite success cannot promote a capability. Every unavailable row retains an open TODO, prerequisite, exact resume command, artifacts, owner, and final reviewer.

### NFR-013 — Convergence guard

Each acceptance criterion is verified at most once after its last relevant change. A lane stops after three distinct fix/verify cycles and reports remaining failures. Identical passing/failing commands are not rerun. Release requires the mission-critical checker, complete evidence matrix, whole interpreter-mode suite, lint, duplication, stub, documentation-freshness, and layout gates.

### NFR-014 — Documentation quality

Scenario manuals shall expose operator flows, outcomes, typed captures, troubleshooting, requirement traceability, and evidence identities while folding executable mechanics. All changed public APIs include accurate doctests or operator examples. Guides shall never advertise a capability unreachable through the actual deployed binary/image.

