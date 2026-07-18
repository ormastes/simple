# Bug: nested `bin/simple test` from SSpec times out the test daemon

Date: 2026-06-28
Status: open
Owner: test runner / SSpec tooling

## Summary

An SSpec scenario that launches a shell wrapper which itself runs
`bin/simple test` can time out the outer test daemon even when the child spec is
small and normally fast. This happened while adding coverage for
`scripts/check/check-gui-web-2d-headless-handoff-prep.shs`.

## Observed Commands

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl --mode=interpreter --clean --fail-fast
sh scripts/check/check-gui-web-2d-headless-handoff-prep.shs
```

## Observed Result

The SSpec version timed out while its scenario invoked the wrapper, and the
wrapper invoked:

```sh
bin/simple test test/03_system/check/gui_web_2d_five_platform_handoff_contract_spec.spl --mode=interpreter --clean --fail-fast
```

Observed failure:

```text
ERROR: test daemon timed out: test/03_system/check/gui_web_2d_headless_handoff_prep_spec.spl
```

The direct wrapper run also reported the nested child as failed when the child
hit the daemon timeout:

```text
gui_web_2d_headless_handoff_prep_reason=five-platform-handoff-spec-failed
```

Running the child SSpec directly after that completed quickly.

## Impact

Wrapper SSpecs can become flaky or slow when they recursively invoke
`bin/simple test`. Agents may misread the timeout as a rendering or handoff
contract failure instead of a test-runner nesting problem.

## Current Workaround

Do not invoke wrappers that run `bin/simple test` from inside another SSpec.
For `gui_web_2d_headless_handoff_prep_spec.spl`, the scenario now checks the
wrapper source contract and generated report boundary. Run the wrapper directly
for executable evidence:

```sh
sh scripts/check/check-gui-web-2d-headless-handoff-prep.shs
```

## Expected Behavior

One of these should become true:

- nested `bin/simple test` calls are isolated from the outer daemon and finish
  reliably, or
- the test runner detects nested test-runner invocation and emits a fast,
  actionable error explaining that the wrapper must be run directly.
