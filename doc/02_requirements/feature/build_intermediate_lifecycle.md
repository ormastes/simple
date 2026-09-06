# Build Intermediate Lifecycle Requirements

- **REQ-BIL-001:** Native build start removes only stale, Simple-owned private staging siblings.
- **REQ-BIL-002:** Successful publication removes debug-useless temporary LLVM object/IR products by default.
- **REQ-BIL-003:** Failed builds remove private staging output by default.
- **REQ-BIL-004:** `--keep-intermediates` and `SIMPLE_KEEP_BUILD_INTERMEDIATES=1` retain diagnostic intermediates.
- **REQ-BIL-005:** `--print-intermediates` and `SIMPLE_PRINT_BUILD_INTERMEDIATES=1` retain and print exact paths.
- **REQ-BIL-006:** Incremental caches, receipts, requested output kinds, and final artifacts are never classified as temporary.
