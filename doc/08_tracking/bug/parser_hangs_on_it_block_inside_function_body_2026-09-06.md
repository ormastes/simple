# Parser hangs forever on a spec `it` block nested inside a function body

Date: 2026-09-06
Status: OPEN (source of the hang worked around; parser defect unfixed)
Area: parser / error recovery

## Symptom

A `.spl` spec file that nests an `it "...":` block inside a `fn` body does not
produce a syntax error. It **hangs**, consuming the whole test budget:

```
SPEC FILE VERDICT: test/01_unit/app/llm_caret/config_spec.spl
  declared>=1 executed=1 passed=0 failed=1 dropped=0
  timeout=1 reason=child-timeout budget_ms=900000
Results: 0 total, 0 passed, 0 failed
```

`Results: 0 total` is the tell — the file never yielded a single example, so the
failure is invisible as a test result. It looks like an infrastructure timeout
rather than a broken file.

## Reproducer shape

`test/01_unit/app/llm_caret/config_spec.spl` had, at lines 49-84, three `it`
blocks indented as statements inside `fn reset_config()`:

```spl
fn reset_config():
    ...
    LOCAL_PYTHON_PATH = "python3"

    it "has default compat base url":        # <- invalid here
        reset_config()
        expect(COMPAT_BASE_URL).to_equal("http://localhost:11434")
```

The last line to make progress was the assignment on the line before the first
`it`. The parser then loops attempting to parse `it` as an expression in
statement position and never terminates or reports.

## Impact

This is a **silent, unbounded** failure mode. It cost 900 seconds per run and
reported zero examples, so the file's real contents — 36 examples, of which 28
were failing — stayed completely hidden behind the timeout for as long as the
corruption existed. A syntax error would have surfaced all of that immediately.

## What was done

The spec was restructured so the misplaced blocks live in a module-level
`describe`, after which the file completes in ~50s and its real failures became
visible. That fixes the FILE, not the parser.

## What the parser should do

Encountering a spec-DSL block (or any construct not valid in statement position)
inside a function body should be a **syntax error with a location**, not a
non-terminating parse. Two independent hardening asks:

1. The parser must not loop on an unexpected token in statement position — error
   recovery should consume or report, never spin.
2. The test runner should distinguish "child timed out having produced zero
   examples" from an ordinary slow file loudly enough that it is not mistaken
   for infrastructure flake. It already prints `reason=child-timeout`; that this
   sat unexamined suggests the signal needs to be harder to ignore.

## Related

`scripts/check/check-outline-parse-terminates.shs` exists for the
parse-termination class but is not in the push tier (it ERRORs without a
deployed `bin/simple`, which most push hosts lack) — see `.claude/rules/vcs.md`,
"Honestly NOT wired". A file like this one is exactly what that guard is for.

Binary measured: `bin/release/aarch64-unknown-linux-gnu/simple`,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed). Not verified on a
self-hosted binary — none exists on this host.
