# Bug: Resource family inference fails for rt_image family

**Status:** Open
**Date:** 2026-08-07
**Component:** WP-D convention inference engine (`src/compiler/35.semantics/resource_families.spl`)

## Problem

Spec `test/01_unit/compiler/resource/resource_family_inference_spec.spl:45-63` fails with:
```
✗ infers rt_image_* with load acquire, free release
  expected true to equal false
```

### Input
```simple
resource_families.infer_family_conventions("rt_image", [
    "rt_image_load",
    "rt_image_width",
    "rt_image_height",
    "rt_image_free",
])
```

### Expected
- Success (is_success() → true)
- acquire_verb="load"
- release_verb="free"

### Actual
- Failure: `is_success()` returns false
- Engine returns an error state

### Similarity
The test pattern is identical to the passing `rt_file_*` test at line 25-43, which succeeds with the same structure (acquire verb, method verbs, release verb).

## Unblock Condition

Debug why:
- rt_file family (open, read, write, close) classifies successfully
- rt_image family (load, width, height, free) returns an error

Likely root causes:
- Module-level verb-list initialization (recently wrapped in functions) not taking effect
- Verb matching logic (is_release_verb, is_acquire_verb) not being called correctly
- Deduplication or error-reporting logic incorrectly triggering for this input

**File:Line:** `test/01_unit/compiler/resource/resource_family_inference_spec.spl:45-63`

## Verification

Once fixed, the failing spec should turn green:
```bash
bin/simple test test/01_unit/compiler/resource/resource_family_inference_spec.spl
# Expected: 17 total, 17 passed, 0 failed
```
