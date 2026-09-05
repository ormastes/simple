# SimpleOS aligned allocation ownership boundary

## Status

Mitigated: over-aligned allocation is honestly unavailable pending an
allocator-owned representation.

## Defect

`simpleos_alloc.c` previously returned either an anonymous direct mmap result
or an aligned interior pointer from an over-allocation. Neither pointer had
metadata understood by `simpleos_dlmalloc.c`, so a valid `free()` could not
reclaim it. Its size/page-rounding additions could also wrap before mapping.

## Current contract

The primary allocator proves 16-byte payload alignment. `posix_memalign` uses
that owned allocation only at or below that alignment; larger requests return
`ENOMEM` without modifying the caller's output pointer. `aligned_alloc` also
enforces its size-multiple requirement, and `valloc`/`pvalloc` fail with
`ENOMEM` instead of manufacturing unowned page-aligned pointers.

## Evidence

`test/01_unit/os/libc/simpleos_aligned_alloc_safety_test.c` compiles and runs
with strict C warnings. It verifies a freeable 16-byte result and failure
semantics for over-alignment, invalid alignment/size, and page-aligned APIs.

## Follow-up

To support alignment above 16 bytes, add a registered aligned-allocation block
format to the dlmalloc owner and make `free`/`realloc` recognize it before
advertising those requests as supported.
