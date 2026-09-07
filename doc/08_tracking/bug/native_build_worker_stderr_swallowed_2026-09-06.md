# native-build discards the worker's stderr, hiding the real error

Status: OPEN (pre-existing; surfaced while building the dynamic-runtime lane)
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
