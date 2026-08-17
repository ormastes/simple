# interpreter_extern registration wiring clobbered — 19/36 specs red in test/01_unit/compiler/interpreter_extern

Date: 2026-08-17
Status: FIXED in source (mod.rs wiring restored); deployed/seed binaries still stale until next seed rebuild + redeploy
Cluster: `test/01_unit/compiler/interpreter_extern/` — 19/36 failed (glfw 4, sdl3 4, capability_gap 10, file_char_device 1)

## Root cause

Two unrelated commits on 2026-08-05 each carried a stale-snapshot clobber of
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, silently deleting
extern-dispatch wiring that lanes R1/R3 had just landed:

- `9c80ba664160` ("feat(wm-lane): W1 FrameClock port") — deleted 21 lines:
  `pub mod glfw;`, `pub mod sdl3;`, and the `rt_glfw_*` / `rt_sdl3_*`
  prefix-dispatch arms (lane R1, originally landed in `2325ece03219`).
- `cb71c629f611` (bootstrap-stage sync commit) — deleted `pub mod capability_gap;`
  and the `capability_gap::matches/dispatch` arm (lane R3) that intercepts
  `rt_webgpu_* / rt_vk_* / rt_gui_* / rt_lyon_* / rt_gamepad_*` before the
  generic "unknown extern function" fallthrough.

The module FILES (`glfw.rs`, `sdl3.rs`, `capability_gap.rs`) survived in-tree
but became orphans — declared nowhere, so cargo never compiled them and no
guard fired (this is the same failure family as
`check-runtime-api-regression-push.shs`'s incident: text/tree guards are blind
to a deleted `mod` declaration; the crate still compiles because the arms and
the declaration were removed together).

Symptom in every failing spec: the probe child emits the generic
`error: semantic: unknown extern function: rt_...` instead of the family guard
/ capability-gap text the specs assert.

Additional orphan module files with no `mod` declaration in mod.rs (not part of
this failing cluster, filed here for follow-up): `vulkan.rs`, `counterpart.rs`,
`packed_span.rs`.

## Fix applied (this session)

Restored in `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`:
`pub mod glfw; pub mod sdl3;` (after `pub mod sdl2;`),
`pub mod capability_gap;` (after `pub mod oneapi;`), the `rt_glfw_*`/`rt_sdl3_*`
dispatch arms after the `rt_sdl2_` arm, and the `capability_gap::matches` arm
immediately before the `dynamic_sffi` fallback — content identical to the
deleted hunks of `2325ece03219` / pre-`cb71c629f611`.

Verified by building the seed in an isolated worktree (HEAD + this mod.rs fix)
and re-running the probe fixtures + the four spec files against it via
`SIMPLE_TEST_BINARY` (see verification section below / spec output).

## Blocker found while verifying: shared working tree does not compile

`cargo check` in the shared tree fails with
`E0432: no simple_core_runtime_archive_is_current in pipeline::native_project::tools`
— UNCOMMITTED working-copy edits to `native_project/config.rs` + `tests.rs`
(identity-archive design) call a function that the working-copy `tools.rs`
(stale-runtime-source design, commit `1f4121930a8`) no longer defines. This is
another parallel-session half-merge, in-flight and uncommitted; not repaired
here to avoid clobbering that session. Committed HEAD is self-consistent.

## Per-spec notes

- `glfw_registration_spec.spl` (4 red) — needs restored `rt_glfw_*` arm; fixed
  by this wiring restore once a seed containing it is deployed/self-heals.
- `sdl3_registration_spec.spl` (4 red) — same, `rt_sdl3_*` arm.
- `capability_gap_spec.spl` (10 red) — same, capability_gap arm; probes expect
  "capability gap" text naming the family instead of the generic unknown-extern.
- `file_char_device_registration_spec.spl` (1 red) — DIFFERENT cause: spec was
  stale, asserting the OLD design (verbatim `const char* path` C copy of
  `rt_file_is_char_device` in `runtime_native_gpu_stub.c`) that was
  deliberately removed as a dual-ABI defect per
  `doc/08_tracking/bug/rt_file_is_char_device_dejit_and_dual_abi_2026-08-10.md`.
  Spec rewritten to assert the current design (canonical `(ptr, len)` ABI in
  runtime.c, gpu stub forbids re-adding a copy, extern-table registration).
- `test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl`
  (6/7) — the remaining red ("declares exactly one return type repo-wide") is a
  DELIBERATE known-failing convergence tracker per its own header and
  `doc/08_tracking/bug/rt_file_read_bytes_declared_with_six_return_types_2026-08-09.md`;
  left RED by policy (do not relax).

## Unblock condition

The four registration specs go green when the child binary they probe
(`bin/simple`, or the `src/compiler_rust/target/{release,debug}/simple`
self-heal fallback) is rebuilt from a tree containing the restored wiring. The
shared tree's cargo breakage above must be resolved (by the owning session
committing or reverting its native_project half-merge) before an in-place
`target/release` rebuild can succeed.
