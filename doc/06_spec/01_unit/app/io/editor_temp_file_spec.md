# Editor temporary file lifecycle

**Source:** `test/01_unit/app/io/editor_temp_file_spec.spl`  
**Updated:** 2026-09-02  
**Result:** 2 scenarios specified; execution is pending a self-hosted runtime
with `test` command support.

## Scenarios

1. Creates two distinct files through exclusive creation, refuses replacement,
   reads exact content with the bounded no-follow reader, and removes both.
2. Rejects path-bearing kind and extension labels before filesystem access.
