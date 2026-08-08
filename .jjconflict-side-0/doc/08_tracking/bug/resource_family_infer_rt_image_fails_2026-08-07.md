# Bug: Resource family inference fails for rt_image family

**Status:** FIXED
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

## Root Cause

The `acquire_verbs()` verb list at `src/compiler/35.semantics/resource_families.spl:8-9` was missing "load" as a recognized acquire verb. The rt_image family's "rt_image_load" verb was being classified as a method (unrecognized) instead of acquire, leaving the family with no acquire verb but a valid release verb ("free"). This caused correct classification success but with acquire_verb=nil, failing the spec assertion.

## Fix

Added "load" to the acquire_verbs list:
```
fn acquire_verbs() -> [text]:
    ["open", "create", "new", "alloc", "acquire", "copy", "clone", "load"]
```

"load" semantically represents resource acquisition (loading/reading data structures like images, tensors, buffers), matching the pattern of other acquire verbs.

## Verification

Fixed spec now passes:
```bash
bin/simple test test/01_unit/compiler/resource/resource_family_inference_spec.spl
# Results: 17 total, 17 passed, 0 failed
```
