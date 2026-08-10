# A large module `"""..."""` docstring + subprocess-heavy `it` blocks silently false-greens later assertions

**Date:** 2026-08-08
**Status:** OPEN, narrowed 2026-08-10 — NOT reproducible on a genuinely
Linux-built seed binary with the doc's own repro shape; root cause NOT
diagnosed (compiler-internal; out of scope for the task that found it, per
instruction to record rather than fix a difficult failure). The original
report's platform-unconfirmed flag is resolved: this is evidence the trigger
is Windows-(.exe)-specific, or at minimum not present on Linux under the
tested shape.
**Severity:** high — a spec file can report 100% pass while containing a
provably-false assertion; `--clean` does NOT avoid it
**Component:** `simple test` runner, most likely the SSpec doc-comment/module-docstring
parser interacting with per-example evaluation for `it` blocks whose body calls
`process_run` (real subprocess execution, multi-hundred-ms to multi-second
runtime)
**Related:** `doc/08_tracking/bug/sspec_test_path_false_green_undercount_2026-07-20.md`,
`doc/08_tracking/bug/bare_assert_statement_vacuity_2026-08-02.md`,
`doc/08_tracking/bug/bdd_expect_eq_comparison_hard_fail_ignores_chained_matcher_2026-07-20.md`
— same "spec-DSL false-green" family, but this is a DIFFERENT specific
trigger (module docstring + subprocess `it`, not a matcher-desugar bug) and
was not covered by any of those fixes.

## Discovery context

Found while writing `test/03_system/check/windows_symlink_checkout_guard_spec.spl`
(a new regression spec for the Windows symlink-checkout fix, same session).
Deliberately broke one assertion to sanity-check the harness actually
evaluates it (standard practice before trusting a new spec's green result) —
and it stayed green. Bisected down to a minimal, clean repro below.

## Minimal repro

```simple
"""
# <any title>

<~70+ lines of arbitrary markdown prose — the exact content does not appear to
matter, only that the docstring is large; see "What was NOT the trigger"
below for the size floor this was not narrowed below>
"""

use std.io_runtime.{file_read, process_run}
use std.spec.*

describe "repro":
    it "first, genuinely passes":
        val (stdout, _stderr, code) = process_run("sh", ["-c", "echo ok"])
        expect(code).to_equal(0)

    it "second, DELIBERATELY WRONG":
        val (_stdout, _stderr, code) = process_run("sh", ["-c", "some real multi-step shell command"])
        expect(code).to_equal(0)
        val output = file_read("some/real/output/file")
        expect(output).to_contain("A STRING THAT PROVABLY DOES NOT APPEAR")
```

Run: `bin/simple test <file> --clean` (verified via
`SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple.exe test <file> --clean`,
a June-2026-built Windows Rust-seed binary — NOT the April self-hosted
`bin/simple`, see the separate, unrelated finding below).

**Result: `Passed: 2, Failed: 0`** — the deliberately-false `to_contain` never
fires.

## What WAS confirmed as the trigger (bisected, each step independently re-run)

| Variant | Result |
|---|---|
| Full 5-`it` real spec (2 describes, ~200 lines incl. a 73-line docstring), one assertion broken | **FALSE GREEN** (5/5 passed) — reproduced 3 times independently |
| Same file, `# @tag:` comment line removed, docstring kept | **STILL FALSE GREEN** (5/5) — ruled out the tag comment as the cause (early hypothesis, disproved) |
| 73-line docstring + only 3 of the 5 `it` blocks (drop the 2 materializer/PowerShell ones) | **FALSE GREEN** (3/3) |
| 73-line docstring + only 2 `it` blocks (1 passing selftest-check, 1 broken) | **FALSE GREEN** (2/2) — smallest confirmed trigger |
| Same 2 `it` blocks, docstring removed entirely (plain `use` + `describe`) | **Correctly FAILED** (1/1, 1 failure) — proves the docstring is necessary |
| Same 2 `it` blocks + docstring, but both blocks replaced with trivial no-subprocess assertions (`expect(1).to_equal(...)`) | **Correctly FAILED** — proves a bare docstring is not sufficient; the `it` bodies must do real subprocess work |
| 2 quick trivial `it` blocks, NO docstring, one wrong | Correctly FAILED |
| 3 sequential `git init`-invoking `it` blocks, NO docstring, last wrong | Correctly FAILED |
| 3 `process_run` + `file_read` + `to_contain` blocks, NO docstring, middle or last wrong | Correctly FAILED (both positions tested) |
| 1 isolated subprocess-heavy `it` block (no docstring, no sibling blocks), ~5s runtime, wrong | Correctly FAILED |
| Same isolated block + a preceding trivial `it`, no docstring | Correctly FAILED |
| Same isolated block + a preceding REAL selftest-invoking `it` (2 blocks total), no docstring | Correctly FAILED |
| 5s `sleep`-padded `it` (no real complexity, no docstring), wrong assertion after the sleep | Correctly FAILED — rules out raw wall-clock duration alone as the trigger |

So: **neither** (a) a large docstring alone, **nor** (b) multiple subprocess-
heavy `it` blocks alone, **nor** (c) long wall-clock duration alone reproduces
this. Only the **combination** of a large leading module docstring **and**
at least two `it` blocks where the failing one performs real subprocess work
via `process_run` reproduces it.

## What was NOT narrowed further (time-boxed; flagging rather than exhausting)

- The exact minimum docstring size/shape was not bisected below 73 lines —
  it is unknown whether a 10-line or 30-line docstring also triggers it.
- Whether the SECOND `it`'s subprocess call specifically (vs. the FIRST's) is
  what matters, or whether both being subprocess-heavy is required, was not
  isolated — the one 2-block repro that reproduced had block 1 = real
  `process_run` (a `--selftest` invocation, ~1-2s) and block 2 = real
  `process_run` (a multi-step git fixture, ~5-10s). It's possible a
  trivial-then-subprocess or subprocess-then-trivial ordering behaves
  differently; not tested.
- Not tested on a genuinely Linux-built binary — only against a Windows
  (`.exe`) June-2026 build of the Rust seed. It is UNKNOWN whether this is
  Windows-specific or a general defect in the seed's SSpec runner regardless
  of host OS. Flagging as unconfirmed rather than asserting either way.
- No attempt was made to trace this into the interpreter/runner source itself
  (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` and neighbors,
  per the related docs' file pointers) — this doc is a black-box
  characterization only.

## Impact

Any spec file combining a substantial module-level `"""` docstring (the
house style this codebase's testing.md explicitly recommends — "Write specs
manual-first... user-voice `"""..."""` docstrings") with `it` blocks that
shell out via `process_run` — which describes a large fraction of the
`test/03_system/check/*.shs`-contract specs in this directory alone (dozens
of examples) — is at risk of silently reporting green regardless of whether
the assertions inside those blocks are actually true. `--clean` does not
avoid it (confirmed: every repro above used `--clean`).

## Mitigation used for the spec that found this

`test/03_system/check/windows_symlink_checkout_guard_spec.spl` (added this
session) DOES carry a full module docstring per house style and DOES have
process_run-based `it` blocks, so it plausibly sits inside the trigger
combination. Verification for THAT spec was instead done by:

1. Running each shell fixture manually, directly in a raw shell (not through
   `simple test` at all) and confirming the guard/materializer scripts'
   real output matches what the spec asserts.
2. Running the FULL original spec content once (unmodified, correct) — green,
   consistent with the manual verification.
3. Deliberately breaking single assertions in SEPARATE, MINIMAL reproduction
   files that stayed OUTSIDE the trigger combination (either short-running,
   or docstring-free) specifically so the sanity-check itself would be
   trustworthy — this is the same bisection work documented above.

This is a workaround for verifying one spec, not a fix — any other spec in
the combination's blast radius has no equivalent manual assurance unless
someone else has separately checked it.

## Suggested follow-up

1. Bisect the docstring size/shape trigger threshold.
2. Trace whether the SSpec doc-comment scanner (used for
   `spipe-docgen`/manual generation, since the codebase explicitly
   encourages doc-comment-driven specs) shares a buffer, index, or cache with
   the per-`it` pass/fail bookkeeping that a large preceding docstring could
   overflow, offset, or truncate.
3. Re-run this repro against a genuinely Linux-built self-hosted or seed
   binary to determine if this is Windows-specific.
4. Given the size of the affected surface (docstring-style specs are the
   HOUSE STYLE per testing.md), this should be escalated in priority once
   picked up — it undermines trust in exactly the kind of spec the codebase
   is steering authors toward writing.

## 2026-08-10 Linux re-verification

Reproduced the doc's shape (73-line module docstring, 2 `it` blocks, first
genuinely passing via `process_run("sh", ...)`, second deliberately wrong —
`process_run` succeeds but the assertion checks stdout `.to_contain(...)` for
a string that provably does not appear) on a genuinely Linux-built binary:
`bin/simple` here resolves to `bin/release/x86_64-unknown-linux-gnu/simple`
(the Rust seed — no self-hosted pure-Simple binary is currently deployed in
this working copy).

```
$ SIMPLE_TIMEOUT_SECONDS=600 bin/simple test <repro.spl> --clean
SPEC FILE VERDICT: ... declared>=2 executed=2 passed=1 failed=1 dropped=0
Results: 2 total, 1 passed, 1 failed
```

**Result: correctly FAILED (1/2)** — the false green does NOT reproduce on
Linux with this repro shape and this (seed) binary. This directly answers one
of the doc's open questions ("Not tested on a genuinely Linux-built binary...
UNKNOWN whether this is Windows-specific") — on the tested shape it is either
Windows-specific or specific to the exact seed build used in the original
report (a June-2026 Windows `.exe`), not a general defect present in the
current Linux seed.

This does not fully close the doc: the exact 5-`it`/2-describe/`--selftest`+
multi-step-git-fixture combination from the original discovery context was
not re-run verbatim (this session used a smaller, deliberately-minimal 2-block
shape per the doc's own "smallest confirmed trigger" row), and no Windows
environment was available to re-test the original binary. Left OPEN, with
narrowed scope: reproduction now requires either a Windows-built seed or the
untested larger/original shape. No fix attempted — this remains a black-box
characterization, and diagnosing further requires tracing the seed's SSpec
runner internals (`src/compiler_rust/**`), which is out of this session's
edit scope.
