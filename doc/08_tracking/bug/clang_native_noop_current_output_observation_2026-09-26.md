# Clang native no-op lacks a trusted current-output observation

**Status:** Open. **Owner:** P6 Clang/native adapter lane; merge owner Codex.

`src/app/build/clang_policy/native_noop_gate.spl:80` requires the supplied
`observed_output_digest` to equal the prior accepted digest before admitting a
native no-op. `src/app/build/clang_policy/output_observation.spl` now performs a
bounded no-follow byte read, hashes that exact snapshot and returns its bytes
only with `ADMIT_NOOP`. No deployed top-level controller binds the prior receipt
and output path to an accepted target/action and fence or publishes those
captured bytes. The decision function cannot establish those facts from
caller-supplied digests.

**Unblock:** Under exclusive build ownership, derive the output path and prior
digest from the accepted action/output manifest and request identity, call the
new observation helper, and publish its returned bytes without reopening the
original pathname. Missing, changed, unreadable or substituted output must
force a native action or report
`INCOMPLETE`. Verify the exact no-op, missing output, changed bytes, symlink,
replacement race and policy-only native rebuild paths with the self-hosted
runner and the CMake/Ninja fixture. The current session's three-cycle verify
cap prevents claiming a Simple runtime PASS.
