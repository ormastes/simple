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
