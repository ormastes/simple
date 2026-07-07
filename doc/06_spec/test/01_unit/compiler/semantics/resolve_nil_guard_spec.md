# Resolve Nil Guard Specification

> <details>

<!-- sdn-diagram:id=resolve_nil_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resolve_nil_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resolve_nil_guard_spec -> std
resolve_nil_guard_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resolve_nil_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resolve Nil Guard Specification

## Scenarios

### MethodResolver nil guards

#### keeps UFCS working when current_fn_sym is Some(nil)

- var symbols = SymbolTable new
- kind: HirTypeKind Function
- span: Span empty
- Some
- Span empty
- var resolver = MethodResolver new
- resolver current fn sym = Some
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var symbols = SymbolTable.new()
val i64_type = HirType.named("i64")
val ping_type = HirType(
    kind: HirTypeKind.Function([i64_type], i64_type, []),
    span: Span.empty()
)
symbols.define(
    "ping",
    SymbolKind.Function,
    Some(ping_type),
    Span.empty(),
    Visibility.Public,
    false,
    nil
)

var resolver = MethodResolver.new(symbols)
resolver.current_fn_sym = Some(nil)

val args: [HirCallArg] = []
val result = resolver.try_ufcs(i64_type, "ping", args)

expect(result.?).to_equal(true)
```

</details>

#### keeps UFCS optional bindings visible to HIR lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/35.semantics/resolve_strategies.spl")

expect(source.contains("if val resolved_lookup_id = func_sym_id")).to_equal(false)
expect(source).to_contain("val resolved_lookup_id = func_sym_id")
expect(source.contains("if val type_id = type_sym_id")).to_equal(false)
expect(source).to_contain("val type_id = type_sym_id")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MethodResolver nil guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
