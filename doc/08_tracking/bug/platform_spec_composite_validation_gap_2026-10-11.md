# Platform specification helper lacks nested grammar and layer-token validation

Date: 2026-10-11.
Status: open; source-inspected finding, runtime reproduction UNRUN.

## Owner and source evidence

Canonical owner:
`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`.
The `std.test_runner.test_runner_types` interface reexports that owner for
current test-runner consumers. An app-local duplicate exists at
`src/app/test_runner_new/test_runner_types.spl`; it is not the owner imported
by the repaired regression spec.

`execution_mode_from_string` classifies every trimmed input containing an
opening parenthesis as `Composite`, without checking closing parentheses,
nested grammar, or runtime/layer names. Thus source inspection predicts that
`interpreter(remote(baremetal(riscv32))` is admitted as a composite despite its
missing final closing parenthesis.

`execution_mode_has_layer` calls `spec.contains(layer)`. Source inspection
therefore predicts that `interpreter(remoteish(riscv32))` reports remote
execution even though its layer token is not `remote`.
`execution_mode_target_arch` similarly searches architecture substrings;
`interpreter(container(not_riscv32))` can report riscv32 based on a substring.

These are source-derived counterexamples, not executed test evidence.

## Impact

Consumers using these helpers for execution routing can misclassify malformed
or similarly named platform specifications. The API returns a mode directly
and offers no structured error for malformed composite input. Unknown plain
names deliberately fall back to Interpreter, which is a separate existing
behavior and must not be confused with composite validation.

## Follow-up acceptance

Define the compatibility/error policy for invalid composite input, then validate
balanced nested syntax and exact layer/architecture tokens before routing.
Preserve accepted simple-mode normalization and valid composite round trips.
Add executable negative regressions for each counterexample and positive
controls for the original remote bare-metal RISC-V32 specification.

The current bounded spec repair at
`test/03_system/tools/manual/platform_spec_verification_spec.spl` exercises
the production helpers for valid modes and existing plain-name fallback. It
does not assert the false-positive behaviors as desired results, does not fix
this source issue, and makes no remote/container/bare-metal execution claim.
