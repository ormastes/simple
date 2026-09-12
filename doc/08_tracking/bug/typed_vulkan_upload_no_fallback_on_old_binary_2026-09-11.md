# Typed Vulkan rect-batch upload had no working fallback on an old binary (2026-09-11)

**Status:** OPEN (unverified 2026-09-12)

## Symptom

PR #534 added `vulkan_sffi_copy_to_buffer_u32` -> `rt_vulkan_copy_to_buffer_u32`
and wired `_enqueue_rect_batch_gpu`
(`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`) to call it
unconditionally (guarded only by `SIMPLE_VK_RECT_UPLOAD=bytes` to force the old
byte path). The PR's own claim was that the call "declines on the native array
ABI -> byte fallback". That is true for the ABI-mismatch case
(`_vulkan_copy_to_buffer_u32_abi` returns `false` cleanly under the native
array ABI), but false for the case that actually matters here: a **deployed
binary older than this extern's existence**.

On `bin/release/aarch64-apple-darwin-macho/simple` (Sep 7 build, predates
`rt_vulkan_copy_to_buffer_u32`),
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_typed_upload_spec.spl`
gave `7 examples, 5 failures`, every failure
`semantic: unknown extern function: rt_vulkan_copy_to_buffer_u32`.

## Root cause

The interpreter's "unknown extern function" path is a **hard process abort**,
not a per-value failure a caller can guard against. Verified directly:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/release/.../simple run probe.spl
before
error: semantic: unknown extern function: rt_vulkan_copy_to_buffer_u32
$ echo $?
1
```

`"before"` prints, `"after"` never does -- the process dies mid-statement.
Simple has no `try`/`catch` (by design, per `.claude/rules/language.md`), so
there is no way to catch this from calling code. It is a different failure
class from the "unbacked extern returns nil" mechanism documented in
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` (which
covers externs the interpreter's dispatch table KNOWS about but that have no
runtime implementation, and IS value-recoverable) -- this is an extern the
old binary's dispatch table has never heard of at all.

No version/capability probe extern exists in this tree that a caller could
check before calling the typed upload (`grep -rn "extern_available|has_extern|
rt_runtime_version|rt_build_features"` across `src/lib` and the seed's extern
tables: zero hits). Adding one would not help anyway -- an old binary calling
a *newly declared* probe extern hits the identical fatal path.

## Fix

Invert the default: the typed word-upload lane is now **opt-in**
(`SIMPLE_VK_RECT_UPLOAD=u32`), not opt-out. The byte payload -- which every
deployed binary, old or new, supports -- is the default and the universal
fallback. `_VULKAN_RECT_UPLOAD_U32_REQUESTED` in
`backend_vulkan_helpers.spl` replaces `_VULKAN_RECT_UPLOAD_BYTES_FORCED`.

Evidence for telling an extern-unavailable byte fallback apart from an
explicit-request byte fallback (both paint identical pixels): two module-level
vars (`_vulkan_rect_upload_last_mode`, `_vulkan_rect_upload_last_reason`) in
`backend_vulkan_helpers.spl`, read via `Engine2D.vulkan_rect_upload_evidence()`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`), formatted as
`"<mode> reason=<reason>"`:
  - `"bytes reason=typed-not-requested"` -- default path.
  - `"u32 reason=typed-requested"` -- `SIMPLE_VK_RECT_UPLOAD=u32` and the ABI
    accepted it.
  - `"bytes reason=typed-declined"` -- `u32` requested but
    `_vulkan_copy_to_buffer_u32_abi` returned false (native array ABI).

## Evidence

Spec: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_typed_upload_spec.spl`
(now 8 examples, +1 asserting the evidence field).

| binary | env | result |
|---|---|---|
| old (`bin/release/aarch64-apple-darwin-macho/simple`, Sep 7, 26264696 bytes) | unset (default) | **8/8 PASS**, evidence `bytes reason=typed-not-requested` |
| old | `SIMPLE_VK_RECT_UPLOAD=u32` (sabotage) | **6/8 FAIL**, `semantic: unknown extern function: rt_vulkan_copy_to_buffer_u32` |
| fresh seed (`build/cargo-r2/release/simple`, Sep 11, 39334680 bytes) | unset (default) | **8/8 PASS**, evidence `bytes reason=typed-not-requested` |
| fresh seed | `SIMPLE_VK_RECT_UPLOAD=u32` | **8/8 PASS**, evidence `u32 reason=typed-requested` |

Sabotage triple confirmed: green (default, old bin) -> red (forced u32, old
bin) -> green again (fresh seed, u32 requested).

## Files changed

- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl` -- invert
  default, add evidence tracking.
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl` -- `vulkan_rect_upload_evidence()`
  facade.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_batch_typed_upload_spec.spl`
  -- doc update + evidence example.

## Known gap, stated rather than papered over

There is still no general "is this extern backed?" probe in the interpreter
that works without calling the extern. Any future new extern added to a hot
Vulkan/GPU path has the same landmine unless it is opt-in by default the same
way. Filing a general-purpose extern-availability probe is future work, not
done here (`.claude/rules/commands.md`'s "NEVER over-engineer" applies -- this
fix is scoped to the one regressed call site).

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
