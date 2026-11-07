# Sampler name publication and shutdown

Executable owner tests: `src/compiler_rust/compiler/src/interpreter/sampler.rs`, `tests` module. These are Rust owner tests, not generated SSpec output.

## Observe complete name identities

Publish a long expression-kind identity and capture the identity seen by a sampler. Replace the current kind with a one-character name before recording the captured sample. The retained sample must still resolve to the complete long name, and the current sample to the one-character name. Dropping the nested marker must restore the original identity.

## Reuse stack slots while sampling

First exercise both a short and long frame through the production sampler so scheduling cannot make the check vacuous. Sample concurrently while repeatedly reusing a frame slot. The two identity-keyed histogram entries must render their exact expected names. Existing frame and kind attribution tests retain self/inclusive accounting controls.

## Retire a sleeping timer

Start the real timer helper with a 30-second park interval, then stop it from another thread. Its wake-and-join completion must arrive within the bounded two-second test timeout. Once joined, the callback count cannot change. This checks the platform-independent timer helper; it does not exercise the Windows CRT exit hook.

## Evidence

Five tests passed in the isolated offline Cargo harness that compiles the actual owner module, with a two-job build cap and one test thread. The original module separately reproduced mixed pointer/length metadata (35 bytes associated with a one-byte name) without dereferencing the invalid range. Full compiler integration, native Windows lifecycle, and performance checks remain verification-wait; no whole-release qualification is implied.
