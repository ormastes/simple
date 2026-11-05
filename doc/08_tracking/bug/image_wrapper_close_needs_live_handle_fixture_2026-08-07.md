# Resource wrapper double-close on a genuinely-acquired handle is untested (Image + FileLock)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
during WP-J (pilot resource migration,
`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`).

**Re-checked 2026-08-09/10:** `test/fixture/io/tiny_1x1.png` already exists in
the tree (added in a later commit than this doc, `7868b6ab6e2`) and IS a
genuinely valid PNG — `file` confirms `PNG image data, 1 x 1, 8-bit/color
RGBA, non-interlaced`, unlike the "hand-assembled minimal PNG" this doc
originally flagged as suspect. Wrote the live-handle double-close test this
doc calls for (`Image` via `load_image_resource`, close twice, assert no
crash/double-free) and ran it: `load_image_resource` still returned `nil` —
`rt_image_load` returns `0` on this fixture too. Ruled out a path-resolution
bug directly: an absolute-path probe against the same file also returned
`nil` from `rt_image_load`. So the "may be an unrelated path-resolution
issue" alternative in the original Unblock condition is eliminated; this is
specifically the repo's `stb_image` build (`src/runtime/runtime_image.c:28`)
rejecting a real, standards-valid 1x1 RGBA PNG, not an artifact of a
hand-assembled fixture. Did not chase the `stb_image`/`runtime_image.c` C
side further — out of the interpreter-only, non-native-build scope of this
verification pass, and debugging a vendored decoder's rejection of a
technically-tiny image is its own investigation. The new test was written,
confirmed to fail for this reason, and then **reverted** rather than landed
red: it does not add coverage of the double-close guard (the load itself
never succeeds, so the guard is never reached on a live handle), so leaving
it in the tree would only be a duplicate marker for this same doc, not a
stronger regression check. Unblock condition updated below.

**Two wrappers, same root cause.** `FileLock` (`src/lib/nogc_sync_mut/sffi/io.spl`)
hit the identical bug shape one level worse: its original spec fabricated
`FileLock(handle: 5)` — a real fd NUMBER, not a made-up pointer — and called
`.close()`, which invokes the real `rt_file_unlock(fd: i64) -> bool` extern
on that fabricated fd. Unlike `Image`'s fabricated pointer (which failed
loudly), this risked silently interfering with a real, in-use file
descriptor belonging to the test runner process itself (fd 5 could be an
open log file, socket, etc.) rather than crashing — a worse failure mode
because it might not be caught by any assertion. Fixed the same way: kept
only the sentinel(-1)-based idempotency proof, removed the fabricated-live-fd
examples, filed here rather than left in the tree.

## What's covered vs. not

`src/lib/nogc_sync_mut/io/image_sffi.spl`'s `Image.close()` guard —
`if self.handle != 0: rt_image_free(self.handle); self.handle = 0` — is
correct by inspection and its idempotency IS tested against the safe invalid
sentinel (`handle: 0`, guard never reaches the extern call):
`test/01_unit/io/image_sffi_resource_wrapper_spec.spl` "close on invalid
handle is safe".

What is NOT tested: calling `.close()` twice on a handle that was genuinely
returned by `rt_image_load` (a real, live stb_image handle). The original
version of this spec tried to approximate this with a fabricated handle
(`Image(handle: 42, ...)`) and called `.close()` on it — this is undefined
behavior (a real C `free`-family call on a pointer value that was never
allocated by the matching allocator) and reliably crashed the test runner
(`error: test-runner: spec failed`, mid-file, no per-example diagnostic).
That version was reverted; see the comment in the spec file.

## Unblock condition

A real, small, decodable image fixture under `test/fixture/io/` that
`rt_image_load` can successfully decode (confirmed via `file` as a valid PNG,
but a hand-assembled minimal 1x1 PNG did not decode through this repo's
stb_image build — `rt_image_load` returned `0`; root cause not yet
investigated, may be a filter/compression edge case stb_image rejects, or an
unrelated path-resolution issue). Once such a fixture exists: load it for a
genuine handle, call `.close()` twice, and assert the second call does not
crash and does not double-free (this is exactly the kind of live-handle
double-close defect this campaign's `resource`/`sffi_gen` design exists to
prevent by construction once reachable).

## Why this matters, not just a test-authoring nit

The distinction between "guard logic is correct" (proven) and "guard logic is
correct against a REAL OS-level resource" (not proven) is the same
distinction the WP-3.5 lint-redeploy finding drew for lint checks: source
correctness and reachable/verified correctness are not the same claim, and
this repo has been burned before by conflating them.

## Triage 2026-09-13
Reconfirmed: test-coverage gap (double-close on a genuinely-acquired
handle untested), P3, needs a live handle fixture. Left OPEN, no code
change attempted.
## Triage 2026-09-13 (BUGFIX-12 shard 22)

`test/fixture/io/tiny_1x1.png` still present; root cause is
`rt_image_load`/stb_image (`src/runtime/runtime_image.c`) rejecting a
standards-valid 1x1 PNG, a native runtime issue out of scope for `src/lib`.
No new fixture attempted. No code change. Leaving OPEN.

## Triage 2026-11-05 (work/libbug-w6-imgwrap-20261105) — FIXED for Image; FileLock latent

Live-handle fixture UNBLOCKED: `rt_image_load` decodes
`test/fixture/io/tiny_1x1.png` fine under the phase1 test binary
(`build/phase_snapshots/phase1_1793422538/simple`, cwd = worktree root) —
earlier "returns 0" observations do not reproduce there.

With a genuine handle reachable, the double-close defect turned out to be REAL
and worse than "guard correct by inspection": in the spec-runner execution
path, mutation through an `Optional`-unwrapped class binding does not persist
(each access re-materializes a copy; reproduced with a minimal
`class ProbeBox` factory returning `ProbeBox?`). `load_image_resource()`
returned `Image?`, so `img.close()` zeroed only a temporary copy and a second
`img.close()` re-entered `rt_image_free` on the still-live original pointer —
child-died-by-signal (double-free). Plain-constructed `Image(handle: h, ...)`
did NOT reproduce this, which is why `simple run` probes looked healthy.

Fix (src/lib/nogc_sync_mut/io/image_sffi.spl, TDD via
test/01_unit/io/image_sffi_resource_wrapper_spec.spl):
- `load_image_resource(path) -> Image` (non-optional): failure returns the
  invalid sentinel `Image(handle: 0, ...)`; `is_valid()` is the nil-check.
- `Image.close()` is now `me fn close():` (mutating receiver, matching the
  tcp_socket/checkpoint_ring/intent_log consuming-drop idiom).
- Deprecated pair made fail-closed the same way: `load_image(path) ->
  LoadedImageData` (sentinel on failure) and `free_image(img) ->
  LoadedImageData` is now a consuming drop that returns the value with its
  handle zeroed (`img = free_image(img)`; a second call is a defined no-op).
  The old by-value-parameter shape could not be zeroed reliably and made a
  second `free_image()` a double-free on a live handle.

Spec now proves, against a genuinely-acquired stb_image handle: decode of
tiny_1x1.png (1x1x4), double `.close()` no-op without crash/double-free,
`get_pixel` returns 0 after close, and `free_image` double-call fail-closed.
13/13 examples pass. No in-repo callers of the changed functions besides the
spec; `std.io` re-exports and the gc_sync_mut/gc_async_mut/nogc_async_mut
family facades still resolve.

OUT OF SCOPE / remaining: `SffiFileLock.close()`
(src/lib/nogc_sync_mut/sffi/io.spl:208) is still a plain `fn close()` whose
mutation has the same non-persistence exposure once a live fd is used; the
same `Optional`-unwrap hazard applies to `file_lock_acquire()`'s `FileLock?`.
Pre-existing unrelated failures observed on the base commit (not this
change): file_lock_resource_wrapper_spec (`FileLock` renamed to
`SffiFileLock`, import stale) and resource_sffi_pilot_spec (parse error).
The Optional-unwrap mutation loss itself is a seed-binary runtime issue
(compiler/runtime, not src/lib) and should be filed separately.
