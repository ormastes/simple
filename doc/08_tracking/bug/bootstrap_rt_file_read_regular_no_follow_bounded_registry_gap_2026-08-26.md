# Bootstrap registry gap for bounded no-follow file reads

## Status

Open. The bootstrap interpreter cannot resolve
`rt_file_read_regular_no_follow_bounded` even though the no-GC file-operation
owner declares it and the native file-operation integration spec requires it.

## Reproduction

From a clean SFFI worktree on 2026-08-26:

```text
bin/simple test test/02_integration/io/native_ops_file_size_spec.spl --mode=interpreter
```

The first size assertion passes. The regular-file/no-follow case then fails
before its assertion with:

```text
semantic: unknown extern function: rt_file_read_regular_no_follow_bounded
```

## Expected

The bootstrap interpreter registry must expose the same declared bounded
no-follow read contract as the native provider, returning the declared nullable
text transport rather than an unresolved-symbol failure.

## Scope and safety impact

This prevents the integration spec from serving as acceptance evidence for
file-operation SFFI changes. It is not caused by lexical `unsafe(ffi)`
annotations: the source check of the same module succeeds and the symbol was
already named by the test before this report. Do not replace the missing
registration with empty text, a passing skip, or a weak value stub.

## Fix direction

Add the exact typed entry to the bootstrap interpreter extern registry and
cover success, missing-path (`nil`), over-bound failure, and symlink rejection.
Keep the raw return nullable; do not widen it to a fabricated non-null text.

## Related test-surface mismatch

`test/01_unit/io/file_lock_resource_wrapper_spec.spl` currently fails four
examples before file-I/O execution with `semantic: function FileLock not found`.
The active raw owner exposes `file_lock`/`file_unlock`; the distinct legacy
`SffiFileLock` resource lives under `std.nogc_sync_mut.sffi.io`. The test must
either import its actual resource owner or be replaced by a file-ops contract
spec. This is likewise pre-existing and not evidence that a false/zero result
should be fabricated.
