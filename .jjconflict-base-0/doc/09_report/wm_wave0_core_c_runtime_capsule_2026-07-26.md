# WM Wave 0 Core-C Runtime Capsule — 2026-07-26

## Status

**Runtime capsule: ACCEPT. Compiler Wave 0: NOT ADMITTED.**

This report accepts only the immutable direct-C runtime prerequisite. It does
not accept a compiler, host render, device backend, or QEMU receipt.

## Accepted identities

- source: `088da06413217edec9454cd0c24de417a8cd5e65`
- runtime tree: `3dd0db9de03e225a0e16164e0a52a40cc4774902`
- producer:
  `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`
- producer SHA-256:
  `dcdb1903c3ab0e58974f5c3f55c92543aa225cb06780893ddc3eb54259366246`
- archive SHA-256:
  `c4f39c1a74e1979d2680153476199b0d70b626fabb0b01d22cedc4505ca46e74`
- manifest SHA-256:
  `5773db91727ce05bde7c100a64ef77206e4b166c1efc36534e7196d2fadf0003`
- repeated-build receipt SHA-256:
  `e0639408ea1ffd1607251b6c7949c5ccde0d19ae8a09c1643f084b01acd4d0b1`

The retained local artifact is
`build/wm-wave0-088da06413/core-c-bootstrap/`.

## Accepted evidence

- clean `HEAD == origin/main == 088da06413217edec9454cd0c24de417a8cd5e65`
  at capsule capture time;
- 24 local runtime input hashes and 12 object/member hashes recompute;
- CC, AR, and NM executable and version-output hashes recompute;
- Darwin deterministic mode is `ZERO_AR_DATE=1 ar rcs`;
- two complete compile/archive passes are byte-identical;
- `rt_string_free` is a global text symbol with sole provider
  `runtime_native.o`;
- the direct C self-check reports `SELFCHECK PASSED (0 failures)`;
- the producer invokes no Simple compiler, Rust seed, Cargo, native-build, or
  freestanding-stub route.

After capture, `origin/main` advanced to
`3ed22008284c9c2dc2cba5dc42d6a69aed7d5c00`, including compiler changes. Its
runtime tree remains exactly
`3dd0db9de03e225a0e16164e0a52a40cc4774902`, so this runtime archive remains
reusable. Compiler Wave 0 must bind to the newer full source revision.

## Remaining compiler blockers

The one bounded bridge cycle has not been spent:

1. no tracked bridge entry matches the current bootstrap API;
2. `aot_native_project_with_backend_fixed` forces low-memory on and cannot
   preserve the required three-opt-in positive versus no-opt-in negative
   control;
3. the historical pure compiler cannot pass the necessary native-build
   validator and does not implement current no-stub semantics;
4. an independent highest-capability review must accept the final direct
   compile route before execution.

Until these are corrected, no host, SIMD, Vulkan, Metal, x86 QEMU, or ARM QEMU
execution row may claim current-source evidence.
