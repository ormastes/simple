# runtime_api_plugin_spec

> Purpose: Verify Runtime API plugin - AC-1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# runtime_api_plugin_spec

Purpose: Verify Runtime API plugin - AC-1.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/plugin/runtime_api_plugin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Runtime API plugin - AC-1.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### Runtime API plugin - AC-1

#### fixture .so exists (run build_fixtures.shs first)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fixture .so exists (run build_fixtures.shs first)
- fixture .so exists (run build_fixtures.shs first)
   - Expected: rt_file_exists(fixture_library()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fixture .so exists (run build_fixtures.shs first)")
step("fixture .so exists (run build_fixtures.shs first)")
# @req: REQ-FEAT-PLUGIN-RUNTIME-API-PLUGIN-SPEC-001
expect(rt_file_exists(fixture_library())).to_equal(true)
```

</details>

#### use_plugin loads the demo entry

- use_plugin loads the demo entry
- use_plugin loads the demo entry
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("use_plugin loads the demo entry")
step("use_plugin loads the demo entry")
val ok = use_plugin_from(fixture_manifest(), "demo")
expect(ok).to_equal(true)
```

</details>

#### list_plugins reports demo by name

- list_plugins reports demo by name
- list_plugins reports demo by name
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("list_plugins reports demo by name")
step("list_plugins reports demo by name")
val _ok = use_plugin_from(fixture_manifest(), "demo")
val names = list_plugins()
var found = false
for n in names:
    if n == "demo":
        found = true
expect(found).to_equal(true)
```

</details>

#### plugin_call_i64 dispatches simple_demo_add(4, 5) = 9

- plugin_call_i64 dispatches simple_demo_add(4, 5) = 9
- plugin_call_i64 dispatches simple_demo_add(4, 5) = 9
   - Expected: result equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("plugin_call_i64 dispatches simple_demo_add(4, 5) = 9")
step("plugin_call_i64 dispatches simple_demo_add(4, 5) = 9")
val _ok = use_plugin_from(fixture_manifest(), "demo")
val result = plugin_call_i64("simple_demo_add", [4, 5])
expect(result).to_equal(9)
```

</details>

#### plugin_call_i64 returns consistent results across edge values

- plugin_call_i64 returns consistent results across edge values
- plugin_call_i64 returns consistent results across edge values
   - Expected: r1 equals `0`
   - Expected: r2 equals `0`
   - Expected: r3 equals `2000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("plugin_call_i64 returns consistent results across edge values")
step("plugin_call_i64 returns consistent results across edge values")
val _ok = use_plugin_from(fixture_manifest(), "demo")
val r1 = plugin_call_i64("simple_demo_add", [0, 0])
val r2 = plugin_call_i64("simple_demo_add", [-1, 1])
val r3 = plugin_call_i64("simple_demo_add", [1000000, 1000000])
expect(r1).to_equal(0)
expect(r2).to_equal(0)
expect(r3).to_equal(2000000)
```

</details>

#### plugin_call_f64 dispatches simple_demo_add_scaled

- plugin_call_f64 dispatches simple_demo_add_scaled
- plugin_call_f64 dispatches simple_demo_add_scaled
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("plugin_call_f64 dispatches simple_demo_add_scaled")
step("plugin_call_f64 dispatches simple_demo_add_scaled")
val _ok = use_plugin_from(fixture_manifest(), "demo")
val result = plugin_call_f64("simple_demo_add_scaled", [1.25, 2.75, 0.5])
expect(result).to_equal(2.0)
```

</details>

#### use_plugin_from returns false for unknown name

- use_plugin_from returns false for unknown name
- use_plugin_from returns false for unknown name
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("use_plugin_from returns false for unknown name")
step("use_plugin_from returns false for unknown name")
val ok = use_plugin_from(fixture_manifest(), "nonexistent")
expect(ok).to_equal(false)
```

</details>

#### WFFI f64 surface covers scalar plugin calls

- WFFI f64 surface covers scalar plugin calls
- WFFI f64 surface covers scalar plugin calls
   - Expected: plugin_call_f64("simple_demo_add_scaled", [1.0, 2.0, 3.0]) equals `9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("WFFI f64 surface covers scalar plugin calls")
step("WFFI f64 surface covers scalar plugin calls")
# FR-PLUG-0001 resolves the old i64-only carve-out by exposing
# spl_wffi_call_f64 and std.plugin.plugin_call_f64.
expect(plugin_call_f64("simple_demo_add_scaled", [1.0, 2.0, 3.0])).to_equal(9.0)
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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-PLUGIN-RUNTIME-API-PLUGIN-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e835dc06f420832fa5fbcf5851fbc2a6e40ce2e64542b431d6b7e1c185aebc10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e835dc06f420832fa5fbcf5851fbc2a6e40ce2e64542b431d6b7e1c185aebc10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e835dc06f420832fa5fbcf5851fbc2a6e40ce2e64542b431d6b7e1c185aebc10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/plugin/runtime_api_plugin_spec.spl
mirror: doc/06_spec/feature/plugin/runtime_api_plugin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/plugin/runtime_api_plugin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/plugin/runtime_api_plugin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/plugin/runtime_api_plugin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/plugin/runtime_api_plugin_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixture .so exists (run build_fixtures.shs first)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/plugin/runtime_api_plugin_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'use_plugin loads the demo entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/plugin/runtime_api_plugin_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'list_plugins reports demo by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
