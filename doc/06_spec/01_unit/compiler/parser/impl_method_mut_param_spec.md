# Impl Method Mut Param Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Impl Method Mut Param Specification

## Scenarios

### impl method mutable parameters

#### preserves a mutable later parameter after implicit self

- "    fn count
- "
- ast reset
- parser init with path
- parse module body
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `3`
   - Expected: methods.len() equals `1`
   - Expected: decl_get_param_names(methods[0]) equals `["self", "inst", "counts"]`
   - Expected: decl_get_param_muts(methods[0]) equals `[0, 0, 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = (
    "class MutableMethodParam:\n" +
    "    fn count(inst: i64, mut counts: Dict<i64, i64>):\n" +
    "        ()\n" +
    "\n" +
    "val sentinel = 7\n"
)

ast_reset()
parser_init_with_path(source, "impl_method_mut_param_spec.spl")
parse_module_body()

expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decls.len()).to_equal(3)
val methods = decl_get_body(decls[0])
expect(methods.len()).to_equal(1)
expect(decl_get_param_names(methods[0])).to_equal(["self", "inst", "counts"])
expect(decl_get_param_muts(methods[0])).to_equal([0, 0, 1])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/impl_method_mut_param_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- impl method mutable parameters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
