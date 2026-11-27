# Plain `test` on a 1-spec dir panics "invalid MC/DC manifest contract"

- **ID:** `test_single_spec_dir_mcdc_manifest_contract_panic_2026-11-07`
- **Status:** fix-implemented-verification-pending
- **Priority:** P2
- **Area:** `src/lib/nogc_sync_mut/test_runner/` (MC/DC manifest handling, interpreter route)

## Repro

Windows, `bin/simple.exe` at `fe52a1431e6`, a directory holding one trivial spec:

```
describe "trivial":
    it "adds":
        expect(1 + 1).to_equal(2)
```

Command: `bin/simple.exe test <dir>` (no `--coverage`). 56 s, 332 MB peak.

Output:

```
[mcdc] SIMPLE_MCDC_MODE=on: interpreter run is not MC/DC-instrumented; running on the interpreter (use --coverage or native for MC/DC evidence)
  FAIL  ...\onespec\trivial_spec.spl (0 passed, 1 failed, 2535ms) [setup: 23ms]
        Error: error: semantic: panic: test-runner: invalid MC/DC manifest contract
SPEC FILE VERDICT: ...trivial_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 in_development=0 dropped=0
```

Afterwards the doctest pass also reports `error: test-runner: no doctest blocks found` / `SPL Doctest: 0 passed, 1 failed`.

## Expected

A passing trivial spec reports 1 passed; a missing MC/DC manifest on the
interpreter route degrades (as the `[mcdc]` line already announces) instead of panicking.

## 2026-11-08 repair candidate — wait for verification

Owner: `p2runtime-1108`, branch
`work/p2-interpreter-mcdc-wrapper-20261108`. The eventual PR merge records
the integration base; no binary qualification is implied by its source head.

The interpreter executor called `build_coverage_wrapper` after routing explicit
coverage to native. Default-on or dynamic MC/DC therefore inserted a native
manifest prelude into a child that has neither the compiler manifest transport
nor instrumentation. The candidate executes the existing infix-normalized
source directly and removes only cleanup of the no-longer-created wrapper.
Native wrapper construction, manifest validation, and coverage routing remain
unchanged.

`test/02_integration/app/test_runner/interpreter_mcdc_manifest_acceptance.spl`
contains four real child-run cases: passing and failing examples in both `on`
and `dynamic` modes. A separate probe calls the actual interpreter executor;
it requires exact example counts and refuses fabricated MC/DC evidence. The
integration spec requires an explicitly pinned admitted source-matched full
CLI and digest; no seed fallback occurs.
The acceptance harness is an explicitly named file, with neither `_spec.` nor
`_test.` in its filename, so directory discovery does not require this external
producer. Slow tests run by default and are not used as an admission gate here.
Child configuration uses direct CLI arguments
and child-local environment operations rather than a POSIX `env` executable;
the fixture explicitly verifies non-fork interpreter routing and enables
authenticated assertion evidence with `--assert-ran`.
Expected failures must carry the authenticated assertion classification and
both unique actual/expected text sentinel tokens. The child writes a per-case
execution marker from inside the authored example before its assertion, and
the probe verifies that marker's exact mode/outcome identity;
infrastructure failures with the same counts are rejected by default-lane
oracle negative controls. The generated spec imports `std.spec.*` explicitly.
The binary/hash pair checks pin consistency, not admission: operator review
must independently establish that the supplied producer is admitted and
source-compatible before any qualification run. The probe checks the resolved
grandchild path and the pinned bytes before and after execution.

Status: **FIX IMPLEMENTED, VERIFICATION PENDING**. Zero behavioral assertions
have executed: no admitted self-hosted full CLI is available on this host.
Required compiler/lib/MCP/LSP checks and native smokes are likewise unrun.
The original Windows directory-level CLI reproduction and native missing-
manifest negative must still run with an admitted producer. Source inspection
and guard passes do not establish closure. This is not a fixed/landed claim.
