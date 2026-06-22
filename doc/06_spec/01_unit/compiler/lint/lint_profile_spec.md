# Lint Profile Specification

> <details>

<!-- sdn-diagram:id=lint_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_profile_spec -> std
lint_profile_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Profile Specification

## Scenarios

### lint strictness profiles (reliable-mode P0)

#### maps every previously-unmapped lint family to a config name (AC-3)

- Resolve formerly-unconfigurable lint codes
   - Expected: map_lint_code_to_config_name("W001") equals `unused_code`
   - Expected: map_lint_code_to_config_name("S001") equals `unsafe_pattern`
   - Expected: map_lint_code_to_config_name("CC001") equals `concurrency_misuse`
   - Expected: map_lint_code_to_config_name("CLOS001") equals `closure_capture`
   - Expected: map_lint_code_to_config_name("RET001") equals `ignored_return`
   - Expected: map_lint_code_to_config_name("BOOL001") equals `multiline_bool`
   - Expected: map_lint_code_to_config_name("SAFE001") equals `memory_safety`
   - Expected: map_lint_code_to_config_name("W0401") equals `visibility_boundary`
   - Expected: map_lint_code_to_config_name("ST001") equals `style_convention`
   - Expected: map_lint_code_to_config_name("D001") equals `database_integrity`
   - Expected: map_lint_code_to_config_name("TRK001") equals `tracking_traceability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve formerly-unconfigurable lint codes")
expect(map_lint_code_to_config_name("W001")).to_equal("unused_code")
expect(map_lint_code_to_config_name("S001")).to_equal("unsafe_pattern")
expect(map_lint_code_to_config_name("CC001")).to_equal("concurrency_misuse")
expect(map_lint_code_to_config_name("CLOS001")).to_equal("closure_capture")
expect(map_lint_code_to_config_name("RET001")).to_equal("ignored_return")
expect(map_lint_code_to_config_name("BOOL001")).to_equal("multiline_bool")
expect(map_lint_code_to_config_name("SAFE001")).to_equal("memory_safety")
expect(map_lint_code_to_config_name("W0401")).to_equal("visibility_boundary")
expect(map_lint_code_to_config_name("ST001")).to_equal("style_convention")
expect(map_lint_code_to_config_name("D001")).to_equal("database_integrity")
expect(map_lint_code_to_config_name("TRK001")).to_equal("tracking_traceability")
```

</details>

#### lib tier preserves current defaults (AC-1)

- Lib == build_default_levels baseline
   - Expected: lib["primitive_api"] equals `deny`
   - Expected: lib["stub_impl"] equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Lib == build_default_levels baseline")
val lib = profile_default_levels(LintProfile.Lib)
expect(lib["primitive_api"]).to_equal("deny")
expect(lib["stub_impl"]).to_equal("deny")
```

</details>

#### moderate tier downgrades deny defaults to warn (AC-1)

- Moderate is advisory
   - Expected: mod["primitive_api"] equals `warn`
   - Expected: mod["stub_impl"] equals `warn`
   - Expected: mod["export_outside_init"] equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Moderate is advisory")
val mod = profile_default_levels(LintProfile.Moderate)
expect(mod["primitive_api"]).to_equal("warn")
expect(mod["stub_impl"]).to_equal("warn")
expect(mod["export_outside_init"]).to_equal("warn")
```

</details>

#### reliable tier elevates safety + public-surface lints to deny (AC-1)

- Reliable is strictest
   - Expected: rel["unsafe_pattern"] equals `deny`
   - Expected: rel["memory_safety"] equals `deny`
   - Expected: rel["visibility_boundary"] equals `deny`
   - Expected: rel["concurrency_misuse"] equals `deny`
   - Expected: rel["non_exhaustive_match"] equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reliable is strictest")
val rel = profile_default_levels(LintProfile.Reliable)
expect(rel["unsafe_pattern"]).to_equal("deny")
expect(rel["memory_safety"]).to_equal("deny")
expect(rel["visibility_boundary"]).to_equal("deny")
expect(rel["concurrency_misuse"]).to_equal("deny")
expect(rel["non_exhaustive_match"]).to_equal("deny")
```

</details>

#### parses tier names and rejects unknowns (AC-2)

- parse_lint_profile round-trips known tiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("parse_lint_profile round-trips known tiers")
expect(parse_lint_profile("reliable").?).to_be(true)
expect(parse_lint_profile("moderate").?).to_be(true)
expect(parse_lint_profile("lib").?).to_be(true)
expect(parse_lint_profile("bogus").?).to_be(false)
```

</details>

#### unset profile preserves legacy behavior; reliable elevates (AC-6)

- nil profile == today's build_default_levels fallback
- var cfg = LintConfig new
   - Expected: level_name(unset) equals `warn`
- select reliable -> elevated to deny
- cfg set profile
   - Expected: level_name(cfg.get_level("unsafe_pattern")) equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("nil profile == today's build_default_levels fallback")
var cfg = LintConfig.new()
# unsafe_pattern base default is warn -> get_level Warn under no profile
val unset = cfg.get_level("unsafe_pattern")
expect(level_name(unset)).to_equal("warn")
step("select reliable -> elevated to deny")
cfg.set_profile(LintProfile.Reliable)
expect(level_name(cfg.get_level("unsafe_pattern"))).to_equal("deny")
```

</details>

#### sdn [lints] profile= selects a tier (AC-2)

- from_sdn_string parses profile= before the lint-name gate
   - Expected: level_name(cfg.get_level("unsafe_pattern")) equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("from_sdn_string parses profile= before the lint-name gate")
val cfg = LintConfig.from_sdn_string("[lints]\nprofile = \"reliable\"\n")
expect(level_name(cfg.get_level("unsafe_pattern"))).to_equal("deny")
```

</details>

#### @lint_profile() file attribute selects a tier (AC-2)

- apply_file_attributes honors @lint_profile, distinct from @profile(critical)
- var cfg = LintConfig new
- cfg apply file attributes
   - Expected: level_name(cfg.get_level("memory_safety")) equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("apply_file_attributes honors @lint_profile, distinct from @profile(critical)")
var cfg = LintConfig.new()
cfg.apply_file_attributes("@lint_profile(reliable)\n\nfn main():\n    print(\"x\")\n")
expect(level_name(cfg.get_level("memory_safety"))).to_equal("deny")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/lint_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lint strictness profiles (reliable-mode P0)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
