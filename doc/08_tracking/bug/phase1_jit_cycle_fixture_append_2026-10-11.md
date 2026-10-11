# Phase 1 JIT circular-dependency fixture append

## Current failure and repair

Current release `dbca09fd567e6c98dd7f87f5dbc63960fa9e7bd0` reproduces the retained
`jit_instantiator_spec.spl` result: 6 passed, 1 failed. The direct circular
dependency setup invokes `insert("cycle_fn")` on `JitInstantiator.in_progress`,
which is `[text]`. Array insertion interprets its first argument as an index;
the fixture therefore fails with `cannot convert string to int` before calling
the circular dependency behavior.

Use `push("cycle_fn")`, the same list append operation used by the production
instantiator. All seven original assertions and cases remain unchanged. No
production file, runtime, compiler cache, or unrelated worktree file changed.

## Scoped evidence

Evidence directory: `build/phase1-jit-cycle-fixture-20261011` in the shared
workspace. `run.py` retains the diagnostic command and isolated environment.

| Evidence | Result |
| --- | --- |
| Current-release baseline | 6/7, exit 1, 1.83 seconds |
| Repaired fixture | 7/7, exit 0, 2.54 seconds |
| Producer SHA256 | `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb` |
| Repaired spec SHA256 | `b1028aa9787cd2a6b95b4c89c962b62bbedf9f53b61a96980be44cdca0a54266` |

Qualification is **BOOTSTRAP_ONLY_DIAGNOSTIC**. This is a test-only fixture
repair, not production runtime admission. The existing JIT compatibility
implementation fabricates compile bytes/addresses; its tests do not establish
native execution or production JIT qualification. No passing criteria were
replayed. One bounded repair cycle was sufficient.

The global 4,758-row candidate queue remains unchanged; this focused evidence
does not remove a row or upgrade rejected receipts. Production loader drafts
2993 and 2996 retain their admitted runtime and platform verification gates.
