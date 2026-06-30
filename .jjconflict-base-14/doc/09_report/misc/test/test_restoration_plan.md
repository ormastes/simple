# Test Restoration Plan

## Deleted Tests (14 files)

### Group 1: Static Function Spec (1 file) - SIMPLEST
- `test/lib/std/unit/spec/static_fn_spec.spl`
- **Issue:** `CallEventRecorder.new` unsupported path call
- **Fix:** Implement static constructor syntax or fix test

### Group 2: Diagram Tests (5 files) - MEDIUM
- `test/lib/std/unit/diagram/recorder_spec.spl`
- `test/lib/std/unit/diagram/sequence_gen_spec.spl`
- `test/lib/std/unit/diagram/class_gen_spec.spl`
- `test/lib/std/unit/diagram/arch_gen_spec.spl`
- `test/lib/std/integration/diagram/diagram_integration_spec.spl`
- **Issue:** `CallEventRecorder.new`, `rt_diagram_*` FFI functions
- **Fix:** Implement CallEventRecorder class or mock it

### Group 3: ML Tests (2 files) - MEDIUM
- `test/lib/std/integration/ml/simple_math_integration_spec.spl`
- `test/lib/std/integration/ml/tensor_inference_integration.spl`
- **Issue:** `matmul` function, `A.matmul` path call
- **Fix:** Implement matrix multiplication or fix test

### Group 4: Doctest Tests (4 files) - COMPLEX
- `test/lib/std/integration/doctest/discovery_spec.spl`
- `test/lib/std/system/doctest/matcher/matcher_spec.spl`
- `test/lib/std/system/doctest/runner/runner_spec.spl`
- `test/lib/std/system/doctest/doctest_advanced_spec.spl`
- **Issue:** `DoctestRunner.new`, `DiscoveryConfig.default`, `MatchResult::*`
- **Fix:** Implement doctest infrastructure or mock it

### Group 5: Gherkin Test (1 file) - MEDIUM
- `test/lib/std/system/gherkin/gherkin_spec.spl`
- **Issue:** `StepKind` enum not found
- **Fix:** Define StepKind enum

### Group 6: CPU Aware Test (1 file) - COMPLEX
- `test/lib/std/system/test_runner/cpu_aware_spec.spl`
- **Issue:** `process.run` function not found
- **Fix:** Implement process.run or mock it

---

## Implementation Order (by complexity)

1. **static_fn_spec.spl** - Fix constructor syntax issue
2. **gherkin_spec.spl** - Add StepKind enum
3. **ML tests** - Fix matmul path call
4. **Diagram tests** - Implement CallEventRecorder
5. **Doctest tests** - Implement doctest infrastructure
6. **cpu_aware_spec.spl** - Implement process.run

---

## Current Progress

- [ ] Group 1: Static Function Spec
- [ ] Group 2: Gherkin Test
- [ ] Group 3: ML Tests
- [ ] Group 4: Diagram Tests
- [ ] Group 5: Doctest Tests
- [ ] Group 6: CPU Aware Test
