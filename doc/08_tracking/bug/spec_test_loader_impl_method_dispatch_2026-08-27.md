# Spec-test loader fails method dispatch and mangles names for locally-defined classes and helpers

Date: 2026-08-27
Status: LIVE 2026-11-11 — runner8 triage; impl-method dispatch still fails file-globally at tip under BOTH `test` and `run` (seed semantic path, not the test loader); owner: seed/compiler lane. Defects 2 (worked around, 17/17 green) and 3 (no longer reproduces) closed. See addendum at end.
Discovered during: sspec modernization batch (39 docgen-failing specs, /tmp/sspec_census/docgen_fails.txt)

## Summary

Converting legacy `fn main():` print-based specs to the SPipe `describe`/`it`
scenario format (so `bin/simple test` actually executes them) surfaced three
loader/namespace defects that do NOT reproduce for the same code under
`bin/simple run`, and do not reproduce in minimal probes:

1. **Impl-method dispatch failure, file-specific.** In
   `test/01_unit/app/test_runner/core_spec.spl`, calling ANY impl method on a
   locally defined class (`msg.encode(...)`, later `parser.feed(...)`) raises
   `semantic: method \`encode\` not found on type \`ProtocolMessage\`` /
   `... method \`feed\` not found on type \`ProtocolParser\`` when the call is
   reached inside an `it` body (the suite's first 8 tests — free-function calls
   only — execute fine). Under `bin/simple run` at HEAD the same file runs to
   completion (only `TestResults success_rate` fails, see below). Reproduces
   with both `SIMPLE_EXECUTION_MODE=interpreter` and `=jit` under `test`, so it
   is in the test-loading path, not the engine. Minimal probes (class + `me`/`fn`
   impl methods, `[i32]` fields, nested `self.` calls, class defined after the
   calling fn, var receivers, multi-arg `me` methods) all PASS — the trigger is
   something specific to the full file that was not isolated (bisection of the
   real file was attempted; even a truncated variant changed failure mode).
   Workaround applied in-file: `encode` rewritten as free function
   `protocol_message_encode(msg, ...)` (assertions unchanged). The spec remains
   RED on `feed`.

2. **Local helper name collision with DSL builtin.** In
   `test/unit/app/test_runner/client_spec.spl`, a file-local
   `fn assert_true(cond, ...) -> AssertResult` is shadowed by the spec-DSL
   builtin `assert_true` inside `it` bodies: `result.passed` then fails with
   `semantic: undefined field 'passed': cannot access field on value of type
   'nil'`. Workaround: renamed to `local_assert_true`.

3. **Uppercase free-function name mangling.** A free function named
   `ProtocolMessage_encode` called from an `it` body was resolved as
   `test_ProtocolMessage_encode` → `semantic: function
   \`test_ProtocolMessage_encode\` not found`. Lowercase names are unaffected.

## Pre-existing red at HEAD (proven via `git show HEAD:<spec>` restore)

- `test/01_unit/app/test_runner/core_spec.spl`: at HEAD under
  `bin/simple run` it already fails 1/20 — `[FAIL] TestResults success_rate
  (got 0.0)` (JIT f64 result of `(passed as f64 / executed as f64) * 100.0`
  is 0.0). Under `bin/simple test` at HEAD it executed ZERO examples
  (`error: test-runner: spec executed nothing (zero-examples)`), so the
  failure was invisible. Left RED after conversion.

## Related systemic finding

All legacy `fn main():`-style specs in this batch executed ZERO examples under
`bin/simple test` at HEAD — the runner silently reported
`Results: 1 total, 0 passed, 1 failed` (or zero-examples) and never ran the
suite. Their assertions were dead weight until converted to `describe`/`it`.

## Unblock condition

- Isolate the loader condition that breaks impl-method resolution in
  core_spec's shape; fix in the spec loader/semantic path.
- Resolve DSL builtin vs file-local helper precedence (or emit a diagnostic).
- Stop mangling uppercase free-function names in it-body rewrites.
- Investigate the JIT `success_rate` 0.0 divergence for `TestResults`.

## Baremetal / scaffold specs left unfixed (scoring gap, recorded not fixed)

The sspec-maintain scorer has no exemption for specs that are baremetal OS
entry points by design (they cannot run under the host SPipe harness), so they
stay at effective 49 with ORA-001/TRC-003 blockers and cannot be documentized:
- `test/03_system/os/os_full_stack_spec.spl`
- `test/03_system/os/os_network_spec.spl`
- `test/system/os_crypto_spec.spl`
- `test/fixtures/baremetal/trivial_baremetal_spec.spl` (documents the reason in-file)

Pending-implementation scaffolds (`it.skip ... nil`), left as designed:
- `test/03_system/compiler/vhdl_mir_backend_call_port_map_spec.spl`
- `test/03_system/compiler/vhdl_mir_backend_multi_output_spec.spl`

Misfiled / non-executable, pre-existing parse failure at HEAD:
- `test/03_system/check/simpleos_arm64_evidence_tooling_spec.spl` — Rust
  source (`fn source(path: String) -> String {`) in a `.spl` path; parse error
  under `bin/simple test` at HEAD. Move to a Rust test target or rewrite in
  Simple.

Delete candidates (assert nothing, no executable content):
- `test/unit/compiler/common/config_spec.spl` — 5-line header-only stub.
- `test/03_system/app/tooling/feature/warning_allow_root_cause_cleanup_spec.spl`
  — prose Gherkin with no code; content belongs in a requirements doc.

---

## Addendum 2026-11-11 — runner8 P3 triage: LIVE (owner: seed/compiler lane)

Re-triaged on release/1.0.0 tip (worktree `simple-p3-runner8-20261111`), seed
binary tracked `bin/simple.exe` @ 46fe8f6b6def, `SIMPLE_LIB=src`,
`--mode=interpreter --no-cache`.

Per-defect status:

1. **Impl-method dispatch (core_spec) — STILL LIVE, and worse than filed.**
   `test/01_unit/app/test_runner/core_spec.spl` fails with
   `semantic: method `feed` not found on type `object` (receiver value:
   ProtocolParser(...))` under `bin/simple test`. New evidence tonight:
   - It now ALSO reproduces under `bin/simple run` (jit-bail:no-main-fn →
     interpreter fallback → same semantic error after 9 [PASS] lines). The
     filed claim that it "does NOT reproduce under `bin/simple run`" is
     STALE — this is the seed semantic path, not the spec-test loader,
     which moves ownership out of the test runner entirely.
   - Isolation probe: with the three `parser.feed(...)` call sites rewritten
     to a free-function stand-in, the next impl call
     `parser.has_messages()` fails identically. Every impl-method dispatch
     in the file is broken, not one method.
   - Minimal probes (fn defined before the class; `me` method chaining;
     the exact `use std.spec.step` + `use spec.{describe, context, it,
     expect}` import header) all PASS — the trigger is file-global and was
     NOT isolated, matching this doc's own failed bisection note.
   - The in-file `protocol_message_encode` free-function workaround
     (encode) remains; feed/has_messages/pop_message have no such
     stand-ins committed.
2. **DSL builtin shadowing (client_spec) — worked around, spec GREEN.**
   The local helper carries a non-colliding name (`fixture_assert_true`,
   defined at client_spec.spl:435). Seed interpreter lane tonight:
   `client_spec.spl` 17/17 passed. The open question "DSL builtin vs
   file-local helper precedence (or emit a diagnostic)" is a seed
   semantic-path decision, same owner as (1).
3. **Uppercase free-function mangling — NO LONGER REPRODUCES.** The
   uppercase free fn `ProtocolMessage_test_pass(...)` is called at
   core_spec.spl:129 inside `run_suite()` (reached from the it-body) and
   resolves fine — "ProtocolMessage test_pass encoding" PASSes in the run
   log. Consider (3) closed by the 2026-11-09 owner-decision mangled-name
   resolution work unless a fresh repro surfaces.

Why LIVE: the surviving defect is in the seed compiler's semantic pass
(impl registrations dropped file-globally for this shape; both interpreter
and JIT; both `test` and `run` entry points). Fixing it requires the
seed/compiler lane to isolate the shape trigger and rebuild/deploy the
seed — outside a P3 bug-fix lane's authority. The pre-existing
`success_rate` JIT f64 divergence stays bundled with this row's owner.

Owner decision needed: seed/compiler lane — isolate why co-compiled impl
blocks lose method registration in this file's shape; decide DSL builtin
vs file-local helper precedence.


---

## Lane disposition 2026-11-13 (p3-misc-b)

Not pursued in this lane: Defect 1 (impl-method dispatch, file-global) is a seed semantic-path defect live at tip under BOTH test and run per 2026-11-11 runner8 addendum; defects 2/3 closed. Owner: seed/compiler lane.