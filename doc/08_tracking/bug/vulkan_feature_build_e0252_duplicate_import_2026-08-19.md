# simple-runtime fails to compile with `--features vulkan --no-default-features` — E0252 duplicate imports

- **Date:** 2026-08-19
- **Status:** OPEN
- **Severity:** high — blocks all four engine2d Vulkan 8K evidence lanes
- **Found by:** GPU/SIMD verification sweep (render-harden worktree, tip `24bcaa1965b`; identical in simple-main)

## Symptom
`scripts/check/check-engine2d-vulkan-{clear,font,mixed,window}-8k.shs` all run
`cargo build -p simple-runtime --release --no-default-features --features vulkan`
and fail (rc=101):

```
error[E0252]: the name `byte_array_bytes` is defined multiple times
  --> runtime/src/vulkan_graphics_runtime_shader.rs:310:20
  --> runtime/src/vulkan_graphics_runtime_compute.rs:911:20
error[E0252]: the name `RuntimeValue` is defined multiple times   (same two files)
```
4 errors total; the committed content is identical in both worktrees, so this
is landed breakage, not worktree drift.

## Root cause shape
Each file imports `byte_array_bytes`/`RuntimeValue` at the top (`shader.rs:6`)
and again mid-file (`shader.rs:310`, `compute.rs:911`). The duplicate is only
visible under the vulkan feature combination; the default-features build (and
therefore `check-seed-builds-push.shs`, which runs `cargo check --bin simple`
with default features) never compiles this configuration — same fail-open shape
as the 2026-08-11 unbuildable-origin incidents, but along the FEATURE axis
instead of the range axis.

## Fix
Delete the mid-file `use crate::value::{byte_array_bytes, RuntimeValue};` at
`vulkan_graphics_runtime_shader.rs:310` and
`vulkan_graphics_runtime_compute.rs:911` (or cfg-gate them to the branch where
the top import is absent). Not applied in this sweep: the verification lane was
explicitly scoped to not modify `src/compiler_rust/**`.

## Downstream impact
The deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`) was built
without the vulkan feature, so `check-vulkan-engine2d-readback.shs` and
sibling lanes that run `bin/simple` report
`status=Unavailable; reason=Vulkan shared session initialization failed:
runtime-init` — and a vulkan-enabled rebuild is impossible until this E0252 is
fixed. One root cause therefore blocks both the bench lanes (build-time) and
the runtime lanes (probe-time).

## Guard gap (secondary)
Consider extending the seed-build guard (or a sibling) to also
`cargo check -p simple-runtime --no-default-features --features vulkan`, since
four evidence lanes depend on that exact configuration compiling.
