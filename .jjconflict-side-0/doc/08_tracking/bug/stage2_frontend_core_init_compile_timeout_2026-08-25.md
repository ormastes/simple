# Stage-2 full-closure bridge times out compiling frontend core init

Status: fixed by duplicate-only facade cleanup; a later streaming-owner
optional extraction now blocks Stage 3/4 admission.

## Exact evidence

- Immutable admitted Stage-2 source producer SHA-256:
  `112a11f6e9e0076ff44e164aabaf14069aa51e91d2bc0f6af4076e59e55d7004`.
- Diagnostic producer copy SHA-256:
  `7373f609508312cd2dabe2979a19044d4bfb4c9ec0eaecd9eaf0ff857e3ac193`.
  Only three proven `Option<HirModule>` call targets were changed from
  `Poll.unwrap` to the existing `rt_enum_payload`; the admitted original was
  not modified.
- Command shape: full `src/compiler`, `src/app`, and `src/lib` entry closure;
  Cranelift; `runtime-bundle auto` for admitted runtime-authority unresolved
  symbol backfill; `SIMPLE_NO_STUB_FALLBACK=1`; per-file timeout 600 seconds;
  outer timeout 1,800 seconds.
- Retained cache:
  `build/bootstrap/abnormality-source-stage3/x86_64-unknown-linux-gnu/native-objects-LAU8Q9`.
- Final log:
  `build/native_probe/abnormality-source-stage25-full-auto-timeout600.log`.
- Terminal result: exit 1, exactly one failed file:
  `src/compiler/10.frontend/core/__init__.spl: timeout (600s)`.

The preceding 60-second attempt timed out a broad group of backend/driver files.
The cache-preserving 600-second retry eliminated every one of those failures
except this single frontend aggregation module. This is progress, not evidence
for raising an unbounded timeout.

## Resume plan

Owner: frontend aggregation/compile-performance maintainer.

In a fresh bounded session, profile the isolated frontend-core aggregation
compile with the admitted diagnostic producer and retained cache. Determine
whether `__init__.spl` accidentally forces an oversized surface/closure or a
specific type/lowering path is superlinear; split or fix the owner rather than
silently increasing the limit. Re-run this exact full-closure bridge at most
once after the source fix. If it emits an intermediary, use that intermediary
for the unmodified canonical `core-c-bootstrap` Stage-3 command, then admit
Stage 3 and Stage 4 before running feature verification or pushing.

## Resolution evidence

The facade contained 203 exact duplicate export names. A mechanical cleanup
retained every public name once and reduced the file from 665 to 614 lines.
With the same producer, cache, and 600-second per-file limit, the full bridge
then completed: 744 compiled, 0 failed, 28,037 KiB output, SHA-256
`37a15c5d0fe0c4b0b4cfb70509ad4bce148a200d48e9e95aaa00636e275f221d`.
The isolated timeout did not recur.

The subsequently emitted Stage-2.5 producer regresses this same aggregation
compile beyond 600 seconds even after deduplication. That later-producer result
is tracked in `stage25_streaming_surface_owner_poll_unwrap_2026-08-25.md`; it
does not invalidate the older-producer resolution receipt above.
