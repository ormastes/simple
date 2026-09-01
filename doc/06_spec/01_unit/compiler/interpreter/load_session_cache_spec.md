# Load Session Cache Specification

> Purpose: Prove that InterpreterLoadConfig.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Load Session Cache Specification

Purpose: Prove that InterpreterLoadConfig.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SMF-001 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Plan | doc/03_plan/smf_load_enable_plan.md |
| Source | `test/01_unit/compiler/interpreter/load_session_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that InterpreterLoadConfig.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### InterpreterLoadConfig

#### creates default config with correct values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates default config with correct values
- Verify: creates default config with correct values
   - Expected: cfg.prefer_compiled is true
   - Expected: cfg.allow_library_smf is true
   - Expected: cfg.allow_source_fallback is true
   - Expected: cfg.regenerate_stale_smf is false
   - Expected: cfg.compiled_imports is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates default config with correct values")
step("Verify: creates default config with correct values")
# @req: REQ-COMPILER-INTERPRETER-001
val cfg = interpreter_load_config_default()
expect(cfg.prefer_compiled).to_equal(true)
expect(cfg.allow_library_smf).to_equal(true)
expect(cfg.allow_source_fallback).to_equal(true)
expect(cfg.regenerate_stale_smf).to_equal(false)
expect(cfg.compiled_imports).to_equal(false)
```

</details>

#### creates source-only config that disables SMF

- creates source-only config that disables SMF
- Verify: creates source-only config that disables SMF
   - Expected: cfg.prefer_compiled is false
   - Expected: cfg.allow_library_smf is false
   - Expected: cfg.allow_source_fallback is true
   - Expected: cfg.regenerate_stale_smf is false
   - Expected: cfg.compiled_imports is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates source-only config that disables SMF")
step("Verify: creates source-only config that disables SMF")
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

- initializes with empty state
- Verify: initializes with empty state
   - Expected: lsc_target_hit_count() equals `0`
   - Expected: lsc_target_miss_count() equals `0`
   - Expected: lsc_freshness_hit_count() equals `0`
   - Expected: lsc_freshness_miss_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("initializes with empty state")
step("Verify: initializes with empty state")
lsc_init()
expect(lsc_target_hit_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lsc_target_miss_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lsc_freshness_hit_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lsc_freshness_miss_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### caches and retrieves target kind

- caches and retrieves target kind
- Verify: caches and retrieves target kind
   - Expected: kind equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caches and retrieves target kind")
step("Verify: caches and retrieves target kind")
lsc_init()
lsc_cache_target("std.text", "/src/main.spl", "source", "/src/lib/text.spl")
val kind = lsc_get_cached_target_kind("std.text", "/src/main.spl")
expect(kind).to_equal("source")
```

</details>

#### caches and retrieves target path

- caches and retrieves target path
- Verify: caches and retrieves target path
   - Expected: path equals `/cache/math.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caches and retrieves target path")
step("Verify: caches and retrieves target path")
lsc_init()
lsc_cache_target("std.math", "/src/main.spl", "smf", "/cache/math.smf")
val path = lsc_get_cached_target_path("std.math", "/src/main.spl")
expect(path).to_equal("/cache/math.smf")
```

</details>

#### returns empty string for uncached target

- returns empty string for uncached target
- Verify: returns empty string for uncached target
   - Expected: kind equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty string for uncached target")
step("Verify: returns empty string for uncached target")
lsc_init()
val kind = lsc_get_cached_target_kind("unknown.mod", "/src/main.spl")
expect(kind).to_equal("")
```

</details>

#### tracks target hits and misses

- tracks target hits and misses
- Verify: tracks target hits and misses
   - Expected: lsc_target_hit_count() equals `1`
   - Expected: lsc_target_miss_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks target hits and misses")
step("Verify: tracks target hits and misses")
lsc_init()
lsc_cache_target("std.text", "/f.spl", "source", "/lib/text.spl")
lsc_get_cached_target_kind("std.text", "/f.spl")
lsc_get_cached_target_kind("unknown", "/f.spl")
expect(lsc_target_hit_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lsc_target_miss_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### caches freshness as fresh (1)

- caches freshness as fresh (1)
- Verify: caches freshness as fresh (1)
   - Expected: lsc_get_cached_freshness("/src/lib/text.spl") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caches freshness as fresh (1)")
step("Verify: caches freshness as fresh (1)")
lsc_init()
lsc_cache_freshness("/src/lib/text.spl", true)
expect(lsc_get_cached_freshness("/src/lib/text.spl")).to_equal(1)
```

</details>

#### caches freshness as stale (0)

- caches freshness as stale (0)
- Verify: caches freshness as stale (0)
   - Expected: lsc_get_cached_freshness("/src/lib/old.spl") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caches freshness as stale (0)")
step("Verify: caches freshness as stale (0)")
lsc_init()
lsc_cache_freshness("/src/lib/old.spl", false)
expect(lsc_get_cached_freshness("/src/lib/old.spl")).to_equal(0)
```

</details>

#### returns -1 for uncached freshness

- returns -1 for uncached freshness
- Verify: returns -1 for uncached freshness
   - Expected: lsc_get_cached_freshness("/unknown.spl") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns -1 for uncached freshness")
step("Verify: returns -1 for uncached freshness")
lsc_init()
expect(lsc_get_cached_freshness("/unknown.spl")).to_equal(-1)
```

</details>

#### tracks compiled module loading

- tracks compiled module loading
- Verify: tracks compiled module loading
   - Expected: lsc_is_compiled_loaded("std.text") is false
   - Expected: lsc_is_compiled_loaded("std.text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks compiled module loading")
step("Verify: tracks compiled module loading")
lsc_init()
expect(lsc_is_compiled_loaded("std.text")).to_equal(false)
lsc_mark_compiled_loaded("std.text")
expect(lsc_is_compiled_loaded("std.text")).to_equal(true)
```

</details>

#### tracks template metadata

- tracks template metadata
- Verify: tracks template metadata
   - Expected: lsc_has_template_metadata("mod_a") is false
   - Expected: lsc_has_template_metadata("mod_a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks template metadata")
step("Verify: tracks template metadata")
lsc_init()
expect(lsc_has_template_metadata("mod_a")).to_equal(false)
lsc_mark_template_metadata("mod_a", true)
expect(lsc_has_template_metadata("mod_a")).to_equal(true)
```

</details>

#### records and checks regen failures

- records and checks regen failures
- Verify: records and checks regen failures
   - Expected: lsc_has_regen_failure("std.broken") is false
   - Expected: lsc_has_regen_failure("std.broken") is true
   - Expected: lsc_get_regen_failure_reason("std.broken") equals `compile error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records and checks regen failures")
step("Verify: records and checks regen failures")
lsc_init()
expect(lsc_has_regen_failure("std.broken")).to_equal(false)
lsc_record_regen_failure("std.broken", "compile error")
expect(lsc_has_regen_failure("std.broken")).to_equal(true)
expect(lsc_get_regen_failure_reason("std.broken")).to_equal("compile error")
```

</details>

#### invalidates a single module

- invalidates a single module
- Verify: invalidates a single module
   - Expected: lsc_is_compiled_loaded("std.text") is false
   - Expected: lsc_has_template_metadata("std.text") is false
   - Expected: lsc_has_regen_failure("std.text") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidates a single module")
step("Verify: invalidates a single module")
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

#### invalidation removes target and freshness entries for the module

- invalidation removes target and freshness entries for the module
- Verify: invalidation removes target and freshness entries for the module
   - Expected: lsc_get_cached_target_kind("std.text", "/src/main.spl") equals ``
   - Expected: lsc_get_cached_target_path("std.text", "/src/main.spl") equals ``
   - Expected: lsc_get_cached_target_kind("std.text", "/src/other.spl") equals ``
   - Expected: lsc_get_cached_target_path("std.text", "/src/other.spl") equals ``
   - Expected: lsc_get_cached_freshness("/src/lib/text.spl") equals `-1`
   - Expected: lsc_get_cached_freshness("/cache/text.smf") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidation removes target and freshness entries for the module")
step("Verify: invalidation removes target and freshness entries for the module")
lsc_init()
lsc_cache_target("std.text", "/src/main.spl", "source", "/src/lib/text.spl")
lsc_cache_target("std.text", "/src/other.spl", "smf", "/cache/text.smf")
lsc_cache_freshness("/src/lib/text.spl", true)
lsc_cache_freshness("/cache/text.smf", true)
lsc_invalidate_module("std.text")
expect(lsc_get_cached_target_kind("std.text", "/src/main.spl")).to_equal("")
expect(lsc_get_cached_target_path("std.text", "/src/main.spl")).to_equal("")
expect(lsc_get_cached_target_kind("std.text", "/src/other.spl")).to_equal("")
expect(lsc_get_cached_target_path("std.text", "/src/other.spl")).to_equal("")
expect(lsc_get_cached_freshness("/src/lib/text.spl")).to_equal(-1)
expect(lsc_get_cached_freshness("/cache/text.smf")).to_equal(-1)
```

</details>

#### invalidating one module keeps other modules' target and freshness entries

- invalidating one module keeps other modules' target and freshness entries
- Verify: invalidating one module keeps other modules' target and freshness entries
   - Expected: lsc_get_cached_target_kind("mod.a", "/src/main.spl") equals ``
   - Expected: lsc_get_cached_freshness("/src/lib/a.spl") equals `-1`
   - Expected: lsc_get_cached_target_kind("mod.b", "/src/main.spl") equals `smf`
   - Expected: lsc_get_cached_target_path("mod.b", "/src/main.spl") equals `/cache/b.smf`
   - Expected: lsc_get_cached_freshness("/cache/b.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidating one module keeps other modules' target and freshness entries")
step("Verify: invalidating one module keeps other modules' target and freshness entries")
lsc_init()
lsc_cache_target("mod.a", "/src/main.spl", "source", "/src/lib/a.spl")
lsc_cache_target("mod.b", "/src/main.spl", "smf", "/cache/b.smf")
lsc_cache_freshness("/src/lib/a.spl", true)
lsc_cache_freshness("/cache/b.smf", true)
lsc_invalidate_module("mod.a")
expect(lsc_get_cached_target_kind("mod.a", "/src/main.spl")).to_equal("")
expect(lsc_get_cached_freshness("/src/lib/a.spl")).to_equal(-1)
expect(lsc_get_cached_target_kind("mod.b", "/src/main.spl")).to_equal("smf")
expect(lsc_get_cached_target_path("mod.b", "/src/main.spl")).to_equal("/cache/b.smf")
expect(lsc_get_cached_freshness("/cache/b.smf")).to_equal(1)
```

</details>

#### invalidating a module does not evict a prefix-similar module

- invalidating a module does not evict a prefix-similar module
- Verify: invalidating a module does not evict a prefix-similar module
   - Expected: lsc_get_cached_target_kind("mod.ab", "/src/main.spl") equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidating a module does not evict a prefix-similar module")
step("Verify: invalidating a module does not evict a prefix-similar module")
lsc_init()
lsc_cache_target("mod.a", "/src/main.spl", "source", "/src/lib/a.spl")
lsc_cache_target("mod.ab", "/src/main.spl", "source", "/src/lib/ab.spl")
lsc_invalidate_module("mod.a")
expect(lsc_get_cached_target_kind("mod.ab", "/src/main.spl")).to_equal("source")
```

</details>

#### invalidates all caches

- invalidates all caches
- Verify: invalidates all caches
   - Expected: lsc_get_cached_target_kind("m1", "/f.spl") equals ``
   - Expected: lsc_get_cached_freshness("/f.spl") equals `-1`
   - Expected: lsc_is_compiled_loaded("m1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidates all caches")
step("Verify: invalidates all caches")
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
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/smf_load_enable_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-INTERPRETER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b277b4319e933c52e2e9b59adb48e12fad795d7e1d5cf89ba7ad5436a49b3a91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b277b4319e933c52e2e9b59adb48e12fad795d7e1d5cf89ba7ad5436a49b3a91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b277b4319e933c52e2e9b59adb48e12fad795d7e1d5cf89ba7ad5436a49b3a91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/load_session_cache_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/load_session_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/load_session_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/load_session_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/load_session_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/load_session_cache_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default config with correct values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/load_session_cache_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates source-only config that disables SMF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/load_session_cache_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes with empty state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
