# native-build discards the worker's stderr, hiding the real error

Status: SUPERSEDED (pre-existing; surfaced while building the dynamic-runtime lane)
Component: `src/compiler_rust/compiler/src/pipeline/native_project` (worker protocol)

## Symptom

When the native-build worker fails, the parent reports only:

```
error: native-build worker exited with code 1.  interpreter: <seed> (exit code 1)
```

The worker's own diagnostic — the sentence that says WHY — never reaches the
caller's stdout/stderr.

## Measured 2026-09-06

Running an authorized-lane refusal deliberately:

```
$ simple native-build --runtime-bundle dynamic-runtime --entry <non-Stage4 entry> ...
error: native-build worker exited with code 1.  interpreter: ... (exit code 1)
```

`selected_runtime_library` returned
`Err("the dynamic-runtime lane is available only to the Stage4 compiler entry; ...")`,
and that string appears nowhere in the parent's combined output. A grep for it
over the full captured stream returns 0 hits. The `[native-build] FULL stderr
(N bytes) saved to: /tmp/native-build-stderr-<pid>.log` line — emitted on some
paths — is not emitted on this one, so there is not even a file to read.

## Why it matters

Every lane-selection, runtime-discovery and link error is raised inside the
worker. Losing them turns an actionable message into "exit code 1", and it
forces gates to assert on side effects (did a binary appear?) instead of on the
diagnostic. `scripts/check/check-stage4-dynamic-runtime-lane.shs` documents
exactly that workaround at its assertion 2 and must be simplified once this is
fixed.

## Unblock condition

Forward the worker's stderr to the parent (or always write and name the
`/tmp/native-build-stderr-*.log` file), then change that gate's assertion 2 from
"no binary produced" back to matching the refusal text.

---

## Addendum 2026-11-11 (lane boot7) — SUPERSEDED (mechanism fixed; gate flip pending)

The unblock condition's first half — forward the worker's stderr to the parent —
is implemented at the release tip. Verified in source at b364745fdbf8:

- **Live relay**: `process_run_timeout_live` now streams the worker's
  stdout/stderr to the parent AS PRODUCED (comment at
  src/app/cli/native_build_main.spl:2057-2064), so a worker that prints a refusal
  and exits shows its text before the parent even summarises the failure.
- **Failure path**: on `code != 0` (native_build_main.spl:2262-2295) the parent
  front-loads `native_build_last_diagnostic_line(stderr)` as
  `error: native-build worker exited with code N.` + `  worker error: <diag>`
  BEFORE the bulk relay, then relays the full worker stderr via `eprint_bounded`
  (full spill + preserved diagnostics per the fixed truncation path), then the
  worker's stdout when non-empty.
- **Worker side**: the refusal raised by `selected_runtime_library`
  (src/compiler_rust/compiler/src/pipeline/native_project/config.rs:647) propagates
  to the worker's own stderr — the Rust native-build entry prints
  `Build failed: {e}` on Err (src/compiler_rust/driver/src/cli/native_build.rs:770-773)
  and exits 1. With the parent relay, that line now reaches the caller.

Fixing merge on the current release-tip history: 820631c6e5c7 (PR #7545,
2026-11-07) — pickaxe (`-S native_build_last_diagnostic_line`,
`-S "relays the worker's stdout/stderr to ours"`) lands there for
native_build_main.spl.

Seed-smoke verification (2026-11-11, seed 0791c2b7f4a7, interpreter mode):
focused probe spec asserting (1) summary + worker-error line ordered before the
bulk `eprint_bounded(stderr)` relay, (2) bounded worker-stdout relay on failure,
(3) the live-relay comment — 3/3 PASSED. (The pre-existing contract spec
test/01_unit/app/cli_native_build_main_contract_spec.spl cases "prints the
worker's own error line before the crash-prone bulk relay" and "routes the
worker-failure relay through the unambiguous stderr_write" also PASSED; 11 of
its 17 content-matching cases fail on unrelated VHDL/simpleos source text drift,
pre-existing on the tip.)

Pending follow-up (bookkeeping, not a mechanism gap): the gate
scripts/check/check-stage4-dynamic-runtime-lane.shs assertion 2 still asserts
differentially on "no binary produced" and its comment cites this bug; per the
unblock condition it can now be flipped to match the refusal text
("the dynamic-runtime lane is available only to the Stage4 compiler entry").
Not flipped here: the gate runs a native-build --entry-closure fixture, which is
forbidden in this lane.
