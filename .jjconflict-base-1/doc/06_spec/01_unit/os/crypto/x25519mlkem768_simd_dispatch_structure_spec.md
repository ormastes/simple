# X25519mlkem768 Simd Dispatch Structure Specification

> Tests covering X25519MLKEM768 SIMD dispatch structure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Simd Dispatch Structure Specification

## Scenarios

### X25519MLKEM768 SIMD dispatch structure

#### should dispatch once per butterfly group and preserve scalar tails (NFR-010)

- Inspect AVX2 NEON and RVV group loops and receipt accounting
   - Expected: source does not contain `int remaining = start + len - j;`
   - Expected: source does not contain `int width = 0;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect AVX2 NEON and RVV group loops and receipt accounting")
val source = file_read_text("src/runtime/runtime_simd_dispatch.c")
expect(source).to_contain("const int end = start + len;")
expect(source).to_contain("if (backend == 1) {\n                while (j + 8 <= end)")
expect(source).to_contain("if (backend == 2) {\n                while (j + 4 <= end)")
expect(source).to_contain("if (backend == 3 && j < end)")
expect(source).to_contain("(size_t)(end - j)")
expect(source).to_contain("hits += executed_chunks;")
expect(source).to_contain("while (j < end) {")
expect(source.contains("int remaining = start + len - j;")).to_equal(false)
expect(source.contains("int width = 0;")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_simd_dispatch_structure_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 SIMD dispatch structure.
- X25519MLKEM768 SIMD dispatch structure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
