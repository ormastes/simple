# Resource wrapper double-close on a genuinely-acquired handle is untested (Image + FileLock)

**Status:** OPEN. **Filed:** 2026-08-07, during WP-J (pilot resource migration,
`doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`).

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
