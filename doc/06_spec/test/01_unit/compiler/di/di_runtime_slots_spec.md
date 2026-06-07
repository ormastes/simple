# Di Runtime Slots Specification

> 1. di runtime plugin binding

<!-- sdn-diagram:id=di_runtime_slots_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_runtime_slots_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_runtime_slots_spec -> std
di_runtime_slots_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_runtime_slots_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Runtime Slots Specification

## Scenarios

### DI runtime slot plugin bindings

#### resolves a declared scalar runtime slot to a plugin-backed implementation

1. di runtime plugin binding
   - Expected: result.ok is true
   - Expected: result.implementation equals `StripePaymentProvider`
   - Expected: result.startup_scan_count equals `1`
   - Expected: result.hot_resolve_count equals `1`
   - Expected: di_runtime_index_diagnostics(index).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [di_runtime_slot("payment", "PaymentProvider")]
val bindings = [
    di_runtime_plugin_binding("payment", "PaymentProvider", "stripe", "plugins/stripe.so", "StripePaymentProvider", 10)
]
val index = di_runtime_build_slot_index(slots, bindings)
val result = di_runtime_resolve_indexed(index, "payment")

expect(result.ok).to_equal(true)
expect(result.implementation).to_equal("StripePaymentProvider")
expect(result.startup_scan_count).to_equal(1)
expect(result.hot_resolve_count).to_equal(1)
expect(di_runtime_index_diagnostics(index).len()).to_equal(0)
```

</details>

#### rejects undeclared slots, final slots, type mismatches, and unsafe paths

1. di runtime slot
2. di runtime final slot
   - Expected: di_runtime_validate_binding(slots, di_runtime_plugin_binding("missing", "PaymentProvider", "x", "plugins/x.so", "Impl", 1)).kind equals `UndeclaredRuntimeSlot`
   - Expected: di_runtime_validate_binding(slots, di_runtime_plugin_binding("core_logger", "Logger", "x", "plugins/x.so", "Impl", 1)).kind equals `FinalRuntimeSlot`
   - Expected: di_runtime_validate_binding(slots, di_runtime_plugin_binding("payment", "OtherType", "x", "plugins/x.so", "Impl", 1)).kind equals `RuntimeSlotTypeMismatch`
   - Expected: di_runtime_validate_binding(slots, di_runtime_plugin_binding("payment", "PaymentProvider", "x", "/tmp/x.so", "Impl", 1)).kind equals `UnsafeRuntimeSlotPath`
   - Expected: di_runtime_validate_binding(slots, di_runtime_plugin_binding("payment", "PaymentProvider", "x", "../x.so", "Impl", 1)).kind equals `UnsafeRuntimeSlotPath`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [
    di_runtime_slot("payment", "PaymentProvider"),
    di_runtime_final_slot("core_logger", "Logger")
]

expect(di_runtime_validate_binding(slots, di_runtime_plugin_binding("missing", "PaymentProvider", "x", "plugins/x.so", "Impl", 1)).kind).to_equal("UndeclaredRuntimeSlot")
expect(di_runtime_validate_binding(slots, di_runtime_plugin_binding("core_logger", "Logger", "x", "plugins/x.so", "Impl", 1)).kind).to_equal("FinalRuntimeSlot")
expect(di_runtime_validate_binding(slots, di_runtime_plugin_binding("payment", "OtherType", "x", "plugins/x.so", "Impl", 1)).kind).to_equal("RuntimeSlotTypeMismatch")
expect(di_runtime_validate_binding(slots, di_runtime_plugin_binding("payment", "PaymentProvider", "x", "/tmp/x.so", "Impl", 1)).kind).to_equal("UnsafeRuntimeSlotPath")
expect(di_runtime_validate_binding(slots, di_runtime_plugin_binding("payment", "PaymentProvider", "x", "../x.so", "Impl", 1)).kind).to_equal("UnsafeRuntimeSlotPath")
```

</details>

#### orders collection runtime slots deterministically

1. di runtime plugin binding
2. di runtime plugin binding
3. di runtime plugin binding
   - Expected: result.ok is true
   - Expected: result.implementations.len() equals `3`
   - Expected: result.implementations[0] equals `AlphaTool`
   - Expected: result.implementations[1] equals `BetaTool`
   - Expected: result.implementations[2] equals `ZetaTool`
   - Expected: result.startup_scan_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [di_runtime_collection_slot("tools", "ToolPlugin")]
val bindings = [
    di_runtime_plugin_binding("tools", "ToolPlugin", "zeta", "plugins/zeta.so", "ZetaTool", 20),
    di_runtime_plugin_binding("tools", "ToolPlugin", "alpha", "plugins/alpha.so", "AlphaTool", 10),
    di_runtime_plugin_binding("tools", "ToolPlugin", "beta", "plugins/beta.so", "BetaTool", 10)
]
val index = di_runtime_build_slot_index(slots, bindings)
val result = di_runtime_resolve_indexed(index, "tools")

expect(result.ok).to_equal(true)
expect(result.implementations.len()).to_equal(3)
expect(result.implementations[0]).to_equal("AlphaTool")
expect(result.implementations[1]).to_equal("BetaTool")
expect(result.implementations[2]).to_equal("ZetaTool")
expect(result.startup_scan_count).to_equal(3)
```

</details>

#### reports typed diagnostics for missing and duplicate implementations

1. di runtime plugin binding
2. di runtime plugin binding
   - Expected: duplicate.ok is false
   - Expected: duplicate.diagnostic.kind equals `DuplicateRuntimeSlotImplementation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slots = [di_runtime_slot("payment", "PaymentProvider")]
val missing_index = di_runtime_build_slot_index(slots, [])
val missing = di_runtime_resolve_indexed(missing_index, "payment")
expect(missing.ok).to_equal(false)
expect(missing.diagnostic.kind).to_equal("MissingRuntimeSlotImplementation")

val duplicate_index = di_runtime_build_slot_index(slots, [
    di_runtime_plugin_binding("payment", "PaymentProvider", "a", "plugins/a.so", "AProvider", 1),
    di_runtime_plugin_binding("payment", "PaymentProvider", "b", "plugins/b.so", "BProvider", 2)
])
val duplicate = di_runtime_resolve_indexed(duplicate_index, "payment")
expect(duplicate.ok).to_equal(false)
expect(duplicate.diagnostic.kind).to_equal("DuplicateRuntimeSlotImplementation")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/di_runtime_slots_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DI runtime slot plugin bindings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
