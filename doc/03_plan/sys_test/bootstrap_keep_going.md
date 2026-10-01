# Bootstrap collect-all regression plan

## Deterministic decisions

Executable spec: `test/03_system/compiler/driver/hir_shard_recovery_spec.spl`.
It directly calls the shared production decision functions for crash replacement
and aggregate failure. It covers nonzero signal/timeout statuses, no-progress
preflight, successful completion, fail-fast, and independent failure counters.
These tests establish REQ-KG-004/005 decisions; they do not establish process
termination, durable receipts, or cache decoding by themselves.

The same spec directly exercises the production filesystem ledger: A succeeds,
B crashes, and a replacement claims C; another worker's claim stays isolated;
terminal failures cannot be overwritten; uncached success is retained; and
traversal completion requires a receipt for the exact owner. These cases test
durable state transitions but do not launch or terminate compiler processes.

## Process and cache scenarios

| Requirement | Scenario and required observation |
|---|---|
| 001 | Default host invocation continues after a diagnostic and default CI stops new work. Host `--fail-fast` and CI `--keep-going` override defaults; both flag orderings prove the last wins. |
| 002/005 | Frozen inventory A, B, C: A succeeds, B child exits abruptly after claiming B, replacement attempts C; B has one attempt, A remains cached, aggregate is nonzero. |
| 002/004 | Two separate module crashes are each attributed once; remaining independent modules complete, and no final-worker/link marker appears. |
| 003 | Retry the same identity: completed entries decode and are reused; failed/unattempted modules remain work. Change compiler identity, closure surface, mode, or corrupt/truncate the body and observe a miss. |
| 003 | Valid but codec-unsupported module has an explicit uncached completion; it does not become a reusable hit or introduce a new compilation rejection. |
| 004/006 | Diagnostic module and dependent blocked module each get terminal outcomes; independent module succeeds; aggregate remains nonzero. |
| 004/005 | Spawn failure or child death before its first claim produces nonzero and zero replacements. Global prerequisite failures never enter a replacement loop. |
| 004 | A stale previously existing output cannot turn a failed shard pass into success or admission. |
| 005 | A finite inventory of N crashing modules produces at most N attributable module attempts; no terminal claim is reopened. |

Use deterministic fixture children and existing process/file facades. No real
compiler crash or full bootstrap is necessary. Do not replace the production
decision functions with a model inside a test and claim runtime integration.
Preserve fixture logs and record the exact invoked runtime/producer identity.

## Evidence gates

Run each acceptance check once; rerun only a failing check after its relevant
fix, with at most three verification cycles. SSpec/docgen require the admitted
self-hosted runtime; missing runtime support is a reported limitation. Generate
the mirrored manual through `spipe-docgen` and require `0 stubs` before claiming
SPipe completion. Source contracts can supplement an unavailable runtime, but
cannot be reported as behavioral passes.

## Execution status (2026-09-30)

SSpec and SPipe docgen: **UNEXECUTED**. The admitted full CLI/test runner is
unavailable (`bin/release/x86_64-pc-windows-msvc/simple.exe` is absent). The
available bootstrap compiler's full CLI and runner build are blocked on SCV
publication. A bootstrap Hello smoke does not validate a test runner, and the
Rust seed is not an allowed substitute. No generated manual or behavioral PASS
is claimed for this spec.

The final recovery spec contains 32 scenarios: 16 deterministic policy/accounting
decisions, 14 production filesystem ledger/inventory cases, and 2 explicitly
structural source wiring contracts. All remain unexecuted under SSpec.

### Isolated pure policy helper smoke

**PASS**, first attempt. The approved bootstrap-only Windows producer
`60b93e4439227160f74eea916eb9e7252daa5dc9cfc866c8eee91b75861145d8` compiled
an exact copy of `compile_failure_policy.spl` plus a standalone ten-case main.
Build exit: `0`; fixture exit: `0`; output:
`PASS isolated pure policy helper: 10 cases`.

The cases cover host/CI defaults, both explicit overrides, both flag orderings,
explicit environment policy, and CLI precedence over environment. Copied helper
SHA-256: `e730999f362d44dccb121ca8c3e3c14d7fc2a82ba5c58bcd52b04b790afc5c7e`.
The build and link completed in approximately 25 seconds. This proves the isolated
pure helper behavior; it does not qualify the production supervisor, filesystem
ledger, full CLI, or test runner.

Evidence retained under `build/native_probe/keep_going_policy_smoke/`:
`launch.json`, `result.json`, `policy_smoke.spl`, build/run stdout and stderr,
and `cache/phase2/60b93e443922/policy-smoke/`. The existing Hello fixture and cache
were preserved. No retries or blocked SCV/memory investigations were performed.
