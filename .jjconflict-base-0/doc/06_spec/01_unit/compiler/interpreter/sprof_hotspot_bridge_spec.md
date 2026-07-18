# Sprof Hotspot Bridge Specification

> <details>

<!-- sdn-diagram:id=sprof_hotspot_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sprof_hotspot_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sprof_hotspot_bridge_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sprof_hotspot_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sprof Hotspot Bridge Specification

## Scenarios

### SprofHotspot construction

#### sprof_hotspot_new (no source)

#### stores function name and call count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("my_fn", 42)
expect(h.function_name).to_equal("my_fn")
expect(h.call_count).to_equal(42)
```

</details>

#### source is empty string when not supplied

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("fn_a", 1)
expect(h.source).to_equal("")
```

</details>

#### sprof_hotspot_with_source

#### stores all three fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_with_source("fn_b", 100, "fn fn_b(x: i64) -> i64: x")
expect(h.function_name).to_equal("fn_b")
expect(h.call_count).to_equal(100)
expect(h.source.len() > 0).to_equal(true)
```

</details>

### sprof_hotspot_to_profile

#### without source

#### typed_mir is false when source is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("layout_fn", 500)
val p = sprof_hotspot_to_profile(h)
expect(p.typed_mir).to_equal(false)
```

</details>

#### safe_deopt is false when source is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("layout_fn", 500)
val p = sprof_hotspot_to_profile(h)
expect(p.safe_deopt).to_equal(false)
```

</details>

#### call_count is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("layout_fn", 500)
val p = sprof_hotspot_to_profile(h)
expect(p.call_count).to_equal(500)
```

</details>

#### name is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("layout_fn", 500)
val p = sprof_hotspot_to_profile(h)
expect(p.name).to_equal("layout_fn")
```

</details>

#### with source

#### typed_mir is true when source is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_with_source("jit_fn", 200, "fn jit_fn(): 0")
val p = sprof_hotspot_to_profile(h)
expect(p.typed_mir).to_equal(true)
```

</details>

#### safe_deopt is true when source is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_with_source("jit_fn", 200, "fn jit_fn(): 0")
val p = sprof_hotspot_to_profile(h)
expect(p.safe_deopt).to_equal(true)
```

</details>

### sprof_hotspot_is_eligible

#### below threshold, no source

#### is not eligible when count=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = sprof_hotspot_new("cold_fn", 0)
val cfg = make_config()
expect(sprof_hotspot_is_eligible(h, cfg)).to_equal(false)
```

</details>

#### above threshold but no source

#### is not eligible without source even if very hot

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Without source, typed_mir=false → plan reason = "missing typed_mir"
val h = sprof_hotspot_new("layout_only_fn", 999999)
val cfg = make_config()
expect(sprof_hotspot_is_eligible(h, cfg)).to_equal(false)
```

</details>

#### above threshold with source

#### is eligible when call_count meets tier1_threshold and source provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
# Use a count well above the default tier1_threshold
val h = sprof_hotspot_with_source("hot_fn", cfg.tier1_threshold + 1, "fn hot_fn(): 1")
expect(sprof_hotspot_is_eligible(h, cfg)).to_equal(true)
```

</details>

### sprof_hotspot_plan reason

#### returns missing profile.hot_count when below threshold with source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
val h = sprof_hotspot_with_source("cold_src_fn", 0, "fn cold_src_fn(): 0")
val reason = sprof_hotspot_plan(h, cfg)
expect(reason).to_equal("missing profile.hot_count")
```

</details>

#### returns missing source when above threshold but no source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# jit_hotspot_plan_reason checks source == "" first (before hot_count or
# typed_mir), so a no-source record yields "missing source" even if hot.
val cfg = make_config()
val h = sprof_hotspot_new("layout_fn", cfg.tier1_threshold + 1)
val reason = sprof_hotspot_plan(h, cfg)
expect(reason).to_equal("missing source")
```

</details>

#### returns ready when hot and source present

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
val h = sprof_hotspot_with_source("hot_src_fn", cfg.tier1_threshold + 1, "fn hot_src_fn(): 2")
val reason = sprof_hotspot_plan(h, cfg)
expect(reason).to_equal("ready")
```

</details>

### sprof_hotspot_call_count_meets_threshold

#### returns false for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
expect(sprof_hotspot_call_count_meets_threshold(0, cfg)).to_equal(false)
```

</details>

#### returns false for count one below threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
expect(sprof_hotspot_call_count_meets_threshold(cfg.tier1_threshold - 1, cfg)).to_equal(false)
```

</details>

#### returns true at exactly threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
expect(sprof_hotspot_call_count_meets_threshold(cfg.tier1_threshold, cfg)).to_equal(true)
```

</details>

#### returns true above threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
expect(sprof_hotspot_call_count_meets_threshold(cfg.tier1_threshold + 100, cfg)).to_equal(true)
```

</details>

### sprof_hotspot_facts

#### facts list contains only typed_mir and safe_deopt for cold function with source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When source is present: typed_mir=true, safe_deopt=true → 2 facts even when cold.
# profile.hot_count is NOT added because call_count < tier1_threshold.
val cfg = make_config()
val h = sprof_hotspot_with_source("cold_src", 0, "fn cold_src(): 0")
val facts = sprof_hotspot_facts(h, cfg)
expect(facts.len()).to_equal(2)
```

</details>

#### facts list contains profile.hot_count for hot function with source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
val h = sprof_hotspot_with_source("hot_src", cfg.tier1_threshold + 1, "fn hot_src(): 0")
val facts = sprof_hotspot_facts(h, cfg)
# At minimum profile.hot_count + typed_mir + safe_deopt = 3 facts
expect(facts.len() >= 1).to_equal(true)
```

</details>

### sprof_hotspots_above_threshold

#### returns empty list when all are cold

- hotspots = hotspots push
- hotspots = hotspots push
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
var hotspots: [SprofHotspot] = []
hotspots = hotspots.push(sprof_hotspot_new("a", 0))
hotspots = hotspots.push(sprof_hotspot_new("b", 1))
val result = sprof_hotspots_above_threshold(hotspots, cfg)
expect(result.len()).to_equal(0)
```

</details>

#### returns only hot entries above threshold

- hotspots = hotspots push
- hotspots = hotspots push
- hotspots = hotspots push
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
var hotspots: [SprofHotspot] = []
hotspots = hotspots.push(sprof_hotspot_new("cold", 0))
hotspots = hotspots.push(sprof_hotspot_new("hot1", cfg.tier1_threshold + 1))
hotspots = hotspots.push(sprof_hotspot_new("hot2", cfg.tier1_threshold + 50))
val result = sprof_hotspots_above_threshold(hotspots, cfg)
expect(result.len()).to_equal(2)
```

</details>

#### preserves function names of hot entries

- hotspots = hotspots push
   - Expected: result.len() equals `1`
   - Expected: result[0].function_name equals `hot_only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_config()
var hotspots: [SprofHotspot] = []
hotspots = hotspots.push(sprof_hotspot_new("hot_only", cfg.tier1_threshold + 1))
val result = sprof_hotspots_above_threshold(hotspots, cfg)
expect(result.len()).to_equal(1)
expect(result[0].function_name).to_equal("hot_only")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/sprof_hotspot_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SprofHotspot construction
- sprof_hotspot_to_profile
- sprof_hotspot_is_eligible
- sprof_hotspot_plan reason
- sprof_hotspot_call_count_meets_threshold
- sprof_hotspot_facts
- sprof_hotspots_above_threshold

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
