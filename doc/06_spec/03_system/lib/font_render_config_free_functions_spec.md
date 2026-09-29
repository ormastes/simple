# FontRenderConfig identity()/valid() Free-Function Regression Spec

> Regression guard for commit 94a893e77b9 (2026-07-18):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FontRenderConfig identity()/valid() Free-Function Regression Spec

Regression guard for commit 94a893e77b9 (2026-07-18):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/font_render_config_free_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression guard for commit 94a893e77b9 (2026-07-18):
`font_render_config_identity` / `font_render_config_valid` were converted
from instance methods (`config.identity()` / `config.valid()`) to FREE
FUNCTIONS taking `config` as an explicit argument. An instance-method call
is miscompiled on the entry-closure freestanding native path
(`--entry-closure --target x86_64-unknown-none`): the call loads the
callee's own code address into the `self` register (rdi) instead of the
receiver, so every field read on `self` faults (first desktop-frame fault
storm). Free-function calls pass `config` correctly as an ordinary
argument and avoid the miscompile. See
doc/08_tracking/bug/engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17.md
and src/lib/nogc_sync_mut/text_layout/font_types.spl (NOTE, 2026-07-18).

This spec exercises `font_render_config_identity` and
`font_render_config_valid` directly as free functions against both the
canonical default config and hand-built custom configs, so a future
regression back to instance-method call shape (or an identity/validity
logic break) is caught at the pure-Simple level, independent of the
freestanding native-codegen bug that originally motivated the move.

## Scenarios

### FontRenderConfig identity()/valid() free functions

#### the default config for a given size is valid

- the default config for a given size is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the default config for a given size is valid")
val config = font_render_config_default_for_size(16)
assert_true(font_render_config_valid(config))
```

</details>

#### the default config identity string encodes the requested size

- the default config identity string encodes the requested size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the default config identity string encodes the requested size")
val config = font_render_config_default_for_size(24)
val identity = font_render_config_identity(config)
assert_contains(identity, "|size=24|")
assert_contains(identity, "font-config-v1|")
```

</details>

#### two default configs at the same size produce the same identity

- two default configs at the same size produce the same identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("two default configs at the same size produce the same identity")
val config_a = font_render_config_default_for_size(18)
val config_b = font_render_config_default_for_size(18)
assert_equal(font_render_config_identity(config_a), font_render_config_identity(config_b))
```

</details>

#### default configs at different sizes produce different identities

- default configs at different sizes produce different identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default configs at different sizes produce different identities")
val config_a = font_render_config_default_for_size(12)
val config_b = font_render_config_default_for_size(48)
assert_not_equal(font_render_config_identity(config_a), font_render_config_identity(config_b))
```

</details>

#### a custom config with a non-default family/category stays valid and reflects in identity

- a custom config with a non-default family/category stays valid and reflects in identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a custom config with a non-default family/category stays valid and reflects in identity")
val config = FontRenderConfig(
    family: "Custom Sans", category: "sans", language: "en", script: "Latn", size: 20,
    weight: "normal", style: "normal", hinting: "none", antialiasing: "grayscale",
    atlas_policy: "shared-alpha-1024", execution_target: "cpu",
    execution_policy: FontExecutionPolicy.Required
)
assert_true(font_render_config_valid(config))
val identity = font_render_config_identity(config)
assert_contains(identity, "custom sans")
assert_contains(identity, "|target=3:cpu|")
```

</details>

#### an out-of-range size is invalid

- an out-of-range size is invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("an out-of-range size is invalid")
var config = font_render_config_default_for_size(16)
config.size = 0
assert_true(font_render_config_valid(config) == false)
```

</details>

#### an empty family is invalid

- an empty family is invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("an empty family is invalid")
var config = font_render_config_default_for_size(16)
config.family = "   "
assert_true(font_render_config_valid(config) == false)
```

</details>

#### a non-normal weight is invalid

- a non-normal weight is invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a non-normal weight is invalid")
var config = font_render_config_default_for_size(16)
config.weight = "bold"
assert_true(font_render_config_valid(config) == false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `904712403e2b527216a8dd7df912d40a78a3f6dd6196223f460a894380b2cf97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `904712403e2b527216a8dd7df912d40a78a3f6dd6196223f460a894380b2cf97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `904712403e2b527216a8dd7df912d40a78a3f6dd6196223f460a894380b2cf97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/lib/font_render_config_free_functions_spec.spl
mirror: doc/06_spec/03_system/lib/font_render_config_free_functions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/font_render_config_free_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/lib/font_render_config_free_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/lib/font_render_config_free_functions_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the default config for a given size is valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/font_render_config_free_functions_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the default config identity string encodes the requested size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/font_render_config_free_functions_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two default configs at the same size produce the same identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
