# While Basic Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Control Flow |
| Status | Active |
| Type | Unit Spec |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/compiler/control_flow/while_basic_spec.spl` |
| Generator | Manual mirrored SSPEC doc |

## Overview

This unit spec keeps a minimal executable regression for `while` loops inside an
SPipe `it` block. It verifies the loop body executes repeatedly and mutates the
local counter before the final assertion.

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Scenarios

### while in it block

#### basic while loop

```simple
var count = 0
while count < 5:
    count = count + 1
expect(count).to_equal(5)
```
