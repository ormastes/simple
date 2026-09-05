# `f1aa8ec2` ("land Vulkan/SDL2/OpenGL dispatch cleanup") silently reverted 5 sibling registrations

Status: fixed inline by the commit that restores the bucket (a) remainder
(see `doc/08_tracking/bug/interpreter_extern_unreachable_names.md`).

## What happened

Commit `f1aa8ec20ade27182725a5426b6ece9c3362df6c` ("fix(compiler_rust):
interpreter adapter for rt_array_data_ptr_u8; land Vulkan/SDL2/OpenGL
dispatch cleanup") landed on 2026-08-05 11:07 UTC. Its own message says it
"lands mod.rs's Vulkan/SDL2/OpenGL interpreter-dispatch cleanup, which had
been sitting uncommitted in this shared worktree from a separate concurrent
session (~300 lines, stable across 40+ minutes of repeated checks)" and
claims that diff "routes the rt_sdl2_*/rt_opengl_*/rt_oneapi_* families to
their real C implementations instead of dying with 'unknown extern
function'" and "re-registers the rt_io_file_* family".

The actual diff does the **opposite** for every one of those families except
vulkan:

- `pub mod sdl2; pub mod audio; pub mod opengl; pub mod oneapi;` — all four
  module declarations **removed**.
- The four `if name.starts_with("rt_sdl2_"/"rt_audio_"/"rt_opengl_"/"rt_oneapi_")`
  dispatch arms in `call_extern_function_with_values` — all **removed**, with
  no replacement registration added anywhere for these four families.
- `pub mod io_file;` and all 15 `insert_simple!("rt_io_file_*", ...)` rows —
  **removed** (the commit message says "re-registers"; the diff shows a pure
  deletion, hunk `@@ -1290,29 +1268,6 @@`).
- 3 TLS timeout stub functions (`rt_tls_client_connect_address_with_sni_timeout_stub`,
  `rt_tls_client_write_timeout_stub`, `rt_tls_client_read_timeout_stub`) and
  their 3 `insert_simple!` registrations — removed, unrelated to vulkan/sdl2.

Only the **vulkan** portion of the commit is real, deliberate, and correct:
24 `rt_vulkan_*` constant-stub rows were legitimately migrated off the old
prefix-dispatch arm onto new `EXTERN_DISPATCH` table rows
(`gpu::rt_vulkan_graphics_unavailable_fn` etc.), with a dedicated regression
test (`rerouted_vulkan_names_are_not_shadowed_by_stub_rows`) proving the old
stub rows don't shadow the new ones. `pub mod vulkan;` and the old
`rt_vulkan_*` prefix arm are correctly gone — that part of the commit
message is accurate.

## Root cause (best-effort reconstruction)

The commit message's own account is the smoking gun: it describes applying
"~300 lines" of **uncommitted worktree diff** that had been "sitting" in this
shared, multi-session working tree. The base that diff was computed against
must have predated the `rt_audio_*` (`b5e8dd69`), `rt_glfw_*`/`rt_sdl3_*`
(`2325ece0`), and `rt_opengl_*`/`rt_oneapi_*` (`7eb0f507`) registration lanes
landing earlier the same day, plus the earlier `rt_io_file_*` registration.
Applying (or reconstructing/committing) that stale diff against the
now-current tree, then committing the result, silently discarded everything
those intervening lanes added in the same regions of `mod.rs` — exactly the
"stale WC reverts fixes" failure mode this repo has hit before (see
`.claude/rules/vcs.md` § "Sync must never clobber").

## Fix

Restored inline as part of the same push that adds the bucket (a) remainder
(`rt_fb_*`/`rt_image_*`/`rt_simpleos_log_*`+`rt_log_target_*`/
`rt_socket_set_nonblocking`), since that work touches the exact same function
(`call_extern_function_with_values`) and region of `mod.rs`:

- Re-added `pub mod sdl2; pub mod audio; pub mod opengl; pub mod oneapi;`
  and their 4 prefix-dispatch arms, verbatim (content taken from local `git`
  history at `b5e8dd6942f7d72809f137165b85127302de317b` /
  `7eb0f507702a2d20db8d4e5cbf1da96a54da7a98`, not reconstructed from memory).
- Re-added `pub mod io_file;` and its 15 `insert_simple!` rows, verbatim.
- Re-added the 3 TLS timeout stub functions and their 3 registrations,
  verbatim.
- Left every vulkan-related change from `f1aa8ec2` untouched (that part is
  real and correct).
- Left `sffi_array.rs`'s `rt_array_data_ptr_u8_fn` addition from the same
  commit untouched (real and correct; unrelated to this revert).

Verified by error-change (not just re-observation): before restoration,
`rt_audio_backend_name`/`rt_opengl_init` on the freshly-fetched `origin/main`
died with `unknown extern function`; after restoration (rebuilt), both
resolve to their real C implementations again
(`audio_backend=uninitialized`, `opengl_init=-3`).

## Follow-up

None of the restored families' own C sources or dispatch logic changed —
this is a pure re-registration, not a reimplementation. If a future `mod.rs`
change legitimately wants to consolidate `sdl2`/`audio`/`opengl`/`oneapi`
onto the `EXTERN_DISPATCH` table pattern the way vulkan was migrated, that is
a real, separate improvement — but it must ADD table rows before removing
the prefix arm, not remove the arm and leave the families unregistered.
