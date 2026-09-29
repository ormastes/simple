# Custom Block Plugin Specification

> Tests covering AC-2: Custom Block Plugin — add and replace.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Block Plugin Specification

## Scenarios

### AC-2: Custom Block Plugin — add and replace

#### new block registers and is visible

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new block registers and is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new block registers and is visible")
_reset_registry()
val csv_def = BlockDef.create("csv", "raw")
val _ok = register_block(csv_def)
check(is_block("csv"))
val all = list_blocks()
check(all.contains("csv"))
```

</details>

#### block parser-fn is invoked on use

- block parser-fn is invoked on use


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("block parser-fn is invoked on use")
# In-process path: call the parser-fn directly (end-to-end source
# compilation is not testable in interpreter mode).
val payload = "1,2,3"
val result = parse_csv(payload)
check(result == "1,2,3")
```

</details>

#### unregister_block removes the entry

- unregister_block removes the entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unregister_block removes the entry")
_reset_registry()
val csv_def = BlockDef.create("csv", "raw")
val _ok = register_block(csv_def)
check(is_block("csv"))
val removed = unregister_block("csv")
check(removed)
check(not is_block("csv"))
```

</details>

#### with_block scope-registers and auto-cleans

- with_block scope-registers and auto-cleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("with_block scope-registers and auto-cleans")
_reset_registry()
val csv_def = BlockDef.create("csv", "raw")
fn body() -> bool:
    is_block("csv")
val inside = with_block(csv_def, body)
check(inside)
check(not is_block("csv"))
```

</details>

#### replacing a built-in is rejected — built-in stays intact

- replacing a built-in is rejected — built-in stays intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("replacing a built-in is rejected — built-in stays intact")
# register_block now returns false when keyword is already taken.
# Attempt to register a fake 'm' def; registry must reject it and
# the original built-in definition must be unchanged.
_reset_registry()
val original = get_block("m")
val fake_m = BlockDef(kind: "m", mode: "math_fake", description: "fake")
val rejected = register_block(fake_m)
# Must return false — keyword was already taken
check(not rejected)
val after = get_block("m")
# Built-in must still be present and its mode must not have changed
check(is_block("m"))
check(after.mode == original.mode)
```

</details>

#### replace flow: unregister then register succeeds with new def

- replace flow: unregister then register succeeds with new def


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("replace flow: unregister then register succeeds with new def")
_reset_registry()
val csv_v1 = BlockDef.create("csv", "raw")
val _ok1 = register_block(csv_v1)
check(is_block("csv"))
unregister_block("csv")
val csv_v2 = BlockDef(kind: "csv", mode: "normal", description: "csv v2")
val _ok2 = register_block(csv_v2)
check(is_block("csv"))
val current = get_block("csv")
check(current.mode == "normal")
check(current.description == "csv v2")
```

</details>

#### use_plugin semantics: blocks register only after explicit activate_plugin call

- use_plugin semantics: blocks register only after explicit activate_plugin call


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("use_plugin semantics: blocks register only after explicit activate_plugin call")
# Validates the two-phase contract from plugin_startup.spl:
#   Phase 1 (index): plugin hook is registered but blocks NOT yet active
#   Phase 2 (activate): activate_plugin("csv_plugin") fires the hook,
#                       which calls register_block; is_block returns true.
#
# This scenario uses local doubles (same API shape as real module) so it
# runs in interpreter mode without importing compiler.blocks.plugin_startup.
# The companion spec plugin_startup_block_spec.spl imports the real module.
_reset_registry()
_reset_plugin_hooks()

# Phase 1: register the plugin hook (simulates module init of csv_plugin.spl)
fn csv_register() -> bool:
    val csv_def = BlockDef.create("csv", "raw")
    val _r = register_block(csv_def)
    true

register_simple_plugin("csv_plugin", csv_register)

# Before activate: block must NOT be in registry
check(not is_block("csv"))

# Phase 2: activate the plugin
val ok = activate_plugin("csv_plugin")
check(ok)

# After activate: block IS in registry
check(is_block("csv"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/plugin/custom_block_plugin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-2: Custom Block Plugin — add and replace.
- AC-2: Custom Block Plugin — add and replace

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a7b2107db6d2ca7063c9328304c4d820157e6b43510d60731ac7a7be0bef3b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a7b2107db6d2ca7063c9328304c4d820157e6b43510d60731ac7a7be0bef3b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a7b2107db6d2ca7063c9328304c4d820157e6b43510d60731ac7a7be0bef3b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/plugin/custom_block_plugin_spec.spl
mirror: doc/06_spec/feature/plugin/custom_block_plugin_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/plugin/custom_block_plugin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/plugin/custom_block_plugin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/plugin/custom_block_plugin_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new block registers and is visible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/plugin/custom_block_plugin_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'block parser-fn is invoked on use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/plugin/custom_block_plugin_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unregister_block removes the entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
