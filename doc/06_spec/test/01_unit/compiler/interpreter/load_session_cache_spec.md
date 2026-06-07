# Load Session Cache Specification

> Tests for InterpreterLoadConfig and LoadSessionCache — pure data types for caching SMF module resolution decisions in interpreter mode.

<!-- sdn-diagram:id=load_session_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=load_session_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

load_session_cache_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=load_session_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Load Session Cache Specification

Tests for InterpreterLoadConfig and LoadSessionCache — pure data types for caching SMF module resolution decisions in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SMF-001 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Plan | doc/03_plan/smf_load_enable_plan.md |
| Source | `test/01_unit/compiler/interpreter/load_session_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for InterpreterLoadConfig and LoadSessionCache — pure data types
for caching SMF module resolution decisions in interpreter mode.

## Scenarios

### InterpreterLoadConfig

#### creates default config with correct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = interpreter_load_config_default()
expect(cfg.prefer_compiled).to_equal(true)
expect(cfg.allow_library_smf).to_equal(true)
expect(cfg.allow_source_fallback).to_equal(true)
expect(cfg.regenerate_stale_smf).to_equal(false)
expect(cfg.compiled_imports).to_equal(false)
```

</details>

#### creates source-only config that disables SMF

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = interpreter_load_config_source_only()
expect(cfg.prefer_compiled).to_equal(false)
expect(cfg.allow_library_smf).to_equal(false)
expect(cfg.allow_source_fallback).to_equal(true)
expect(cfg.regenerate_stale_smf).to_equal(false)
expect(cfg.compiled_imports).to_equal(false)
```

</details>

### LoadSessionCache

#### initializes with empty state

1. lsc init
   - Expected: lsc_target_hit_count() equals `0`
   - Expected: lsc_target_miss_count() equals `0`
   - Expected: lsc_freshness_hit_count() equals `0`
   - Expected: lsc_freshness_miss_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
expect(lsc_target_hit_count()).to_equal(0)
expect(lsc_target_miss_count()).to_equal(0)
expect(lsc_freshness_hit_count()).to_equal(0)
expect(lsc_freshness_miss_count()).to_equal(0)
```

</details>

#### caches and retrieves target kind

1. lsc init
2. lsc cache target
   - Expected: kind equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_cache_target("std.text", "/src/main.spl", "source", "/src/lib/text.spl")
val kind = lsc_get_cached_target_kind("std.text", "/src/main.spl")
expect(kind).to_equal("source")
```

</details>

#### caches and retrieves target path

1. lsc init
2. lsc cache target
   - Expected: path equals `/cache/math.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_cache_target("std.math", "/src/main.spl", "smf", "/cache/math.smf")
val path = lsc_get_cached_target_path("std.math", "/src/main.spl")
expect(path).to_equal("/cache/math.smf")
```

</details>

#### returns empty string for uncached target

1. lsc init
   - Expected: kind equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
val kind = lsc_get_cached_target_kind("unknown.mod", "/src/main.spl")
expect(kind).to_equal("")
```

</details>

#### tracks target hits and misses

1. lsc init
2. lsc cache target
3. lsc get cached target kind
4. lsc get cached target kind
   - Expected: lsc_target_hit_count() equals `1`
   - Expected: lsc_target_miss_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_cache_target("std.text", "/f.spl", "source", "/lib/text.spl")
lsc_get_cached_target_kind("std.text", "/f.spl")
lsc_get_cached_target_kind("unknown", "/f.spl")
expect(lsc_target_hit_count()).to_equal(1)
expect(lsc_target_miss_count()).to_equal(1)
```

</details>

#### caches freshness as fresh (1)

1. lsc init
2. lsc cache freshness
   - Expected: lsc_get_cached_freshness("/src/lib/text.spl") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_cache_freshness("/src/lib/text.spl", true)
expect(lsc_get_cached_freshness("/src/lib/text.spl")).to_equal(1)
```

</details>

#### caches freshness as stale (0)

1. lsc init
2. lsc cache freshness
   - Expected: lsc_get_cached_freshness("/src/lib/old.spl") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_cache_freshness("/src/lib/old.spl", false)
expect(lsc_get_cached_freshness("/src/lib/old.spl")).to_equal(0)
```

</details>

#### returns -1 for uncached freshness

1. lsc init
   - Expected: lsc_get_cached_freshness("/unknown.spl") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
expect(lsc_get_cached_freshness("/unknown.spl")).to_equal(-1)
```

</details>

#### tracks compiled module loading

1. lsc init
   - Expected: lsc_is_compiled_loaded("std.text") is false
2. lsc mark compiled loaded
   - Expected: lsc_is_compiled_loaded("std.text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
expect(lsc_is_compiled_loaded("std.text")).to_equal(false)
lsc_mark_compiled_loaded("std.text")
expect(lsc_is_compiled_loaded("std.text")).to_equal(true)
```

</details>

#### tracks template metadata

1. lsc init
   - Expected: lsc_has_template_metadata("mod_a") is false
2. lsc mark template metadata
   - Expected: lsc_has_template_metadata("mod_a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
expect(lsc_has_template_metadata("mod_a")).to_equal(false)
lsc_mark_template_metadata("mod_a", true)
expect(lsc_has_template_metadata("mod_a")).to_equal(true)
```

</details>

#### records and checks regen failures

1. lsc init
   - Expected: lsc_has_regen_failure("std.broken") is false
2. lsc record regen failure
   - Expected: lsc_has_regen_failure("std.broken") is true
   - Expected: lsc_get_regen_failure_reason("std.broken") equals `compile error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
expect(lsc_has_regen_failure("std.broken")).to_equal(false)
lsc_record_regen_failure("std.broken", "compile error")
expect(lsc_has_regen_failure("std.broken")).to_equal(true)
expect(lsc_get_regen_failure_reason("std.broken")).to_equal("compile error")
```

</details>

#### invalidates a single module

1. lsc init
2. lsc mark compiled loaded
3. lsc mark template metadata
4. lsc record regen failure
5. lsc invalidate module
   - Expected: lsc_is_compiled_loaded("std.text") is false
   - Expected: lsc_has_template_metadata("std.text") is false
   - Expected: lsc_has_regen_failure("std.text") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_mark_compiled_loaded("std.text")
lsc_mark_template_metadata("std.text", true)
lsc_record_regen_failure("std.text", "err")
lsc_invalidate_module("std.text")
expect(lsc_is_compiled_loaded("std.text")).to_equal(false)
expect(lsc_has_template_metadata("std.text")).to_equal(false)
expect(lsc_has_regen_failure("std.text")).to_equal(false)
```

</details>

#### invalidates all caches

1. lsc init
2. lsc cache target
3. lsc cache freshness
4. lsc mark compiled loaded
5. lsc invalidate all
   - Expected: lsc_get_cached_target_kind("m1", "/f.spl") equals ``
   - Expected: lsc_get_cached_freshness("/f.spl") equals `-1`
   - Expected: lsc_is_compiled_loaded("m1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lsc_init()
lsc_cache_target("m1", "/f.spl", "source", "/p.spl")
lsc_cache_freshness("/f.spl", true)
lsc_mark_compiled_loaded("m1")
lsc_invalidate_all()
expect(lsc_get_cached_target_kind("m1", "/f.spl")).to_equal("")
expect(lsc_get_cached_freshness("/f.spl")).to_equal(-1)
expect(lsc_is_compiled_loaded("m1")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/smf_load_enable_plan.md](doc/03_plan/smf_load_enable_plan.md)


</details>
