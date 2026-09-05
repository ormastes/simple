<!-- codex-design -->
# Backend Layer Artifact and Runtime Matrix NFR

Status: **Selected — NFR Option 2 (practical 95% reachable branch coverage and
100% matrix accounting)**

## NFR-001 — Reachable branch coverage

The owned artifact contract, matrix registry/runner, backend adapters, probe
classification, and receipt validation must reach at least **95% branch
coverage of reachable branches**. The denominator must exclude only branches
proven unreachable in the measured profile (for example, a compile-time OS
guard) and every exclusion must include file, branch, profile, reason, and
normal/highest-capability reviewer approval. Line coverage is supporting
evidence and cannot replace branch coverage.

## NFR-002 — Matrix accounting

The generated ledger must account for **100%** of the Cartesian product of:

- the canonical backend registry;
- the declared environment profiles;
- the ten canonical artifact/runtime stages.

Every cell must be `PASS`, `FAIL`, `SKIP_UNAVAILABLE`, or `NOT_APPLICABLE` with
the required evidence. No absent, unknown, stale, or duplicate cell is allowed.
Matrix accounting is not pass rate: an accounted `FAIL` still blocks release.

## NFR-003 — Baseline release profile

Linux x86_64 pure-Simple shared stages plus available CPU code-generation rows
are required and cannot skip. Platform CI owns Linux AArch64, macOS AArch64,
Windows x86_64, FreeBSD x86_64, SimpleOS/QEMU AArch64, and SimpleOS/QEMU RISC-V
profiles. GPU cells are required on designated GPU runners and evidence-backed
`SKIP_UNAVAILABLE` elsewhere.

## NFR-004 — Determinism and integrity

Canonical text serialization must be byte-identical across two warm runs using
the same producer/target. Every published file must pass size and SHA-256
verification. Known nondeterministic binary sections must be normalized or
explicitly excluded with a documented parser and reviewer approval.

## NFR-005 — Disabled-path cost

With no debug-dump or matrix flag, artifact payload serialization and file I/O
must be zero. On a representative warm native build, instrumentation guards must
add no more than 1% median wall-clock time and no more than 1% peak RSS versus
the same binary with the feature disabled; measure at least five runs and report
the median and maximum RSS.

## NFR-006 — Enabled-path progress and resources

Collect-all mode must emit low-overhead progress containing completed, running,
failed, skipped, and remaining cells. Concurrency must obey configured CPU and
memory limits and must not launch more device/toolchain jobs than the profile
declares safe. Existing valid artifacts may be reused only when producer,
source, options, target, and tool/device identities match.

## NFR-007 — Evidence freshness

Each ledger records source revision, pure-Simple producer digest, target,
toolchain/device identity, fixture digest, start/end time, and artifact paths.
Release evidence is stale if any identity differs from the build being released.

## NFR-008 — Diagnostic safety

Artifact paths must remain beneath the selected dump root after sanitization.
No environment secrets, command-line credentials, or unrelated source files may
enter artifacts or receipts. Temporary files must be deleted after failed
publication where recovery is possible.

## Gate result

The verifier reports `PASS` only when NFR-001 is at least 95%, NFR-002 is 100%,
all required cells pass, no evidence is stale, integrity checks pass, and no
unreviewed coverage exclusion exists.
