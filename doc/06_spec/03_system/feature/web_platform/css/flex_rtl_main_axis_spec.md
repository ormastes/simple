# CSS Flex RTL Main Axis

> Row flex layout composes `direction` with `flex-direction`, keeps the stable
> `order` sort, and applies each wrapped line's gaps, justification, and auto
> margins before lowering nested content through canonical Draw IR.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Status | Active source; qualified execution held |
| Requirements | REQ-WEB-BROWSER-003, 004, 021 |
| Source | `test/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl` |
| Updated | 2026-07-31 |

## Claim Boundary

The scenario proves bounded integer geometry and exact software pixels for LTR,
RTL, direct `row-reverse`, `flex-flow: row-reverse nowrap`, wrapped stable
ordering, a nested descendant, per-line `space-between` plus column gaps, and a
physical auto margin. It does not claim column-axis reversal or native GPU
evidence.

## Scenario

### should place ordered children from main-start for RTL and LTR

1. **Parse the styled document**
   - Parse 8-by-2 nowrap LTR and RTL controls.
   - Parse LTR/RTL direct `row-reverse` controls, an LTR
     `flex-flow: row-reverse nowrap` shorthand control, a 4-by-4 ordered nested
     wrap, and 7-pixel wrapped justification and auto-margin controls.
2. **Resolve the winning computed style**
   - RTL remains the winning `direction`.
   - Both direct reverse controls and the shorthand control retain computed
     `flex_direction=row-reverse`; the value is not collapsed to `row` before
     layout.
3. **Emit canonical Draw IR geometry and paint**
   - RTL row items occupy x=6 and x=4; the LTR negative control uses x=0 and
     x=2.
   - LTR `row-reverse` uses x=6/x=4 while RTL `row-reverse` composes back to
     x=0/x=2.
   - The LTR `flex-flow` shorthand control also uses x=6/x=4.
   - Stable `order` puts the blue item at x=2 and red at x=0 on the first
     wrapped line. The nested 1-by-2 descendant remains attached at `(2,2)`.
   - Per-line `space-between` plus the one-pixel column gap yields x=5/x=0;
     the next line starts at x=5. A physical auto margin also yields x=5/x=0.
4. **Render exact Engine2D pixels**
   - The complete 8-by-2 nowrap, direct reverse, shorthand reverse, 4-by-4
     ordered/nested wrap, 7-by-4 justified wrap, and 7-by-2 auto-margin pixel
     buffers must equal their ARGB oracles.
   - No command may be skipped.

<details>
<summary>Executable SSpec</summary>

The mirrored executable scenario contains the full HTML fixtures, semantic and
Draw IR lookup helpers, exact geometry assertions, and complete pixel arrays.

```simple
step("Parse the styled document")
step("Resolve the winning computed style")
step("Emit canonical Draw IR geometry and paint")
step("Render exact Engine2D pixels")
```

</details>
