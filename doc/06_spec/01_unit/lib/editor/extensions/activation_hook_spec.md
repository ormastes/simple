# activation_hook_spec

> Purpose: Prove that extension activation hooks (L6b).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# activation_hook_spec

Purpose: Prove that extension activation hooks (L6b).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/extensions/activation_hook_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that extension activation hooks (L6b).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### extension activation hooks (L6b)

#### does not run the hook before activation, then runs it exactly once

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not run the hook before activation, then runs it exactly once
- Verify: does not run the hook before activation, then runs it exactly once
   - Expected: _hook_calls equals `0`
   - Expected: host.activation_hook_ran("hook-demo") is false
   - Expected: activated is true
   - Expected: _hook_calls equals `1`
   - Expected: host.activation_hook_ran("hook-demo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not run the hook before activation, then runs it exactly once")
step("Verify: does not run the hook before activation, then runs it exactly once")
# @req: REQ-LIB-EDITOR-001
_hook_calls = 0
val host = ExtensionHost.new()
host.register_manifest(hook_demo_manifest(), "<test>")
host.register_activation_hook("hook-demo", _counting_hook)
expect(_hook_calls).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(host.activation_hook_ran("hook-demo")).to_equal(false)

val activated = host.activate("hook-demo")
expect(activated).to_equal(true)
expect(_hook_calls).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(host.activation_hook_ran("hook-demo")).to_equal(true)
```

</details>

#### does not re-run the hook across a deactivate/activate cycle (guard against re-activation)

- does not re-run the hook across a deactivate/activate cycle (guard against re-activation)
- Verify: does not re-run the hook across a deactivate/activate cycle (guard against re-activation)
   - Expected: _hook_calls equals `1`
   - Expected: host.deactivate("hook-demo") is true
   - Expected: host.activate("hook-demo") is true
   - Expected: _hook_calls equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not re-run the hook across a deactivate/activate cycle (guard against re-activation)")
step("Verify: does not re-run the hook across a deactivate/activate cycle (guard against re-activation)")
_hook_calls = 0
val host = ExtensionHost.new()
host.register_manifest(hook_demo_manifest(), "<test>")
host.register_activation_hook("hook-demo", _counting_hook)
host.activate("hook-demo")
expect(_hook_calls).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(host.deactivate("hook-demo")).to_equal(true)
expect(host.activate("hook-demo")).to_equal(true)
expect(_hook_calls).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### an Err hook becomes a diagnostic and does not crash the host; the extension still activates

- an Err hook becomes a diagnostic and does not crash the host; the extension still activates
- Verify: an Err hook becomes a diagnostic and does not crash the host; the extension still activates
   - Expected: activated is true
   - Expected: host.is_active("hook-fail-demo") is true
   - Expected: host.activation_diagnostic_count() equals `before_diag + 1`
   - Expected: host.last_activation_diagnostic() contains `hook-fail-demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an Err hook becomes a diagnostic and does not crash the host; the extension still activates")
step("Verify: an Err hook becomes a diagnostic and does not crash the host; the extension still activates")
val host = ExtensionHost.new()
host.register_manifest(failing_demo_manifest(), "<test>")
host.register_activation_hook("hook-fail-demo", _failing_hook)
val before_diag = host.activation_diagnostic_count()

val activated = host.activate("hook-fail-demo")
expect(activated).to_equal(true)
expect(host.is_active("hook-fail-demo")).to_equal(true)
expect(host.activation_diagnostic_count()).to_equal(before_diag + 1)
expect(host.last_activation_diagnostic().contains("hook-fail-demo")).to_equal(true)
```

</details>

#### host stays functional after a failing hook: an unrelated extension still activates and dispatches

- host stays functional after a failing hook: an unrelated extension still activates and dispatches
- Verify: host stays functional after a failing hook: an unrelated extension still activates and dispatches
   - Expected: out equals `pong:hi`
   - Expected: "sibling dispatch" equals `should have succeeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host stays functional after a failing hook: an unrelated extension still activates and dispatches")
step("Verify: host stays functional after a failing hook: an unrelated extension still activates and dispatches")
val host = ExtensionHost.new()
host.register_manifest(failing_demo_manifest(), "<test>")
host.register_activation_hook("hook-fail-demo", _failing_hook)
host.activate("hook-fail-demo")

host.register_manifest(sibling_demo_manifest(), "<test>")
host.register_command_handler("hook-sibling-demo", "sibling.ping", "Sibling Ping", sibling_handler)
match host.dispatch_command("sibling.ping", "hi"):
    case Ok(out):
        expect(out).to_equal("pong:hi")
    case Err(_):
        expect("sibling dispatch").to_equal("should have succeeded")
```

</details>

#### an extension with no registered hook activates normally (no-op)

- an extension with no registered hook activates normally (no-op)
- Verify: an extension with no registered hook activates normally (no-op)
   - Expected: host.activate("hook-sibling-demo") is true
   - Expected: host.activation_hook_ran("hook-sibling-demo") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an extension with no registered hook activates normally (no-op)")
step("Verify: an extension with no registered hook activates normally (no-op)")
val host = ExtensionHost.new()
host.register_manifest(sibling_demo_manifest(), "<test>")
expect(host.activate("hook-sibling-demo")).to_equal(true)
expect(host.activation_hook_ran("hook-sibling-demo")).to_equal(false)
```

</details>

#### sheets DOUBLE is reachable via the function registry after activating the builtin through its own onCommand event

- sheets DOUBLE is reachable via the function registry after activating the builtin through its own onCommand event
- Verify: sheets DOUBLE is reachable via the function registry after activating the builtin through its own onCommand event
   - Expected: sheet_function_registry_has("DOUBLE") is false
   - Expected: host.is_active("sheets-function-registry-demo") is false
   - Expected: host.activate_command("sheets.function.double") equals `1`
   - Expected: host.is_active("sheets-function-registry-demo") is true
   - Expected: sheet_function_registry_has("DOUBLE") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sheets DOUBLE is reachable via the function registry after activating the builtin through its own onCommand event")
step("Verify: sheets DOUBLE is reachable via the function registry after activating the builtin through its own onCommand event")
sheet_function_registry_reset()
expect(sheet_function_registry_has("DOUBLE")).to_equal(false)
val host = extension_host_with_builtins()
expect(host.is_active("sheets-function-registry-demo")).to_equal(false)
expect(host.activate_command("sheets.function.double")).to_equal(1)
expect(host.is_active("sheets-function-registry-demo")).to_equal(true)
expect(sheet_function_registry_has("DOUBLE")).to_equal(true)
```

</details>

#### slides title_diagram is reachable via the layout registry after activating the builtin through its own onCommand event

- slides title_diagram is reachable via the layout registry after activating the builtin through its own onCommand event
- Verify: slides title_diagram is reachable via the layout registry after activating the builtin through its own onCommand event
   - Expected: slide_layout_registry_has("title_diagram") is false
   - Expected: host.is_active("slides-layout-registry-demo") is false
   - Expected: host.activate_command("slides.layout.titleDiagram") equals `1`
   - Expected: host.is_active("slides-layout-registry-demo") is true
   - Expected: slide_layout_registry_has("title_diagram") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("slides title_diagram is reachable via the layout registry after activating the builtin through its own onCommand event")
step("Verify: slides title_diagram is reachable via the layout registry after activating the builtin through its own onCommand event")
slide_layout_registry_reset()
expect(slide_layout_registry_has("title_diagram")).to_equal(false)
val host = extension_host_with_builtins()
expect(host.is_active("slides-layout-registry-demo")).to_equal(false)
expect(host.activate_command("slides.layout.titleDiagram")).to_equal(1)
expect(host.is_active("slides-layout-registry-demo")).to_equal(true)
expect(slide_layout_registry_has("title_diagram")).to_equal(true)
```

</details>

### the sheets/slides registry builtins are lazily reachable through their own onCommand event (fixed 2026-07-31)

#### the indexed builtin host runs no activation hook: DOUBLE and title_diagram stay unregistered

- the indexed builtin host runs no activation hook: DOUBLE and title_diagram stay unregistered
- Verify: the indexed builtin host runs no activation hook: DOUBLE and title_diagram stay unregistered
   - Expected: host.active_count() equals `0`
   - Expected: host.activation_hook_ran("sheets-function-registry-demo") is false
   - Expected: host.activation_hook_ran("slides-layout-registry-demo") is false
   - Expected: sheet_function_registry_has("DOUBLE") is false
   - Expected: slide_layout_registry_has("title_diagram") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the indexed builtin host runs no activation hook: DOUBLE and title_diagram stay unregistered")
step("Verify: the indexed builtin host runs no activation hook: DOUBLE and title_diagram stay unregistered")
sheet_function_registry_reset()
slide_layout_registry_reset()
val host = extension_host_with_builtins_indexed()
expect(host.active_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(host.activation_hook_ran("sheets-function-registry-demo")).to_equal(false)
expect(host.activation_hook_ran("slides-layout-registry-demo")).to_equal(false)
expect(sheet_function_registry_has("DOUBLE")).to_equal(false)
expect(slide_layout_registry_has("title_diagram")).to_equal(false)
```

</details>

#### activate_command reaches the sheets/slides registry builtins through their own declared command id

- activate_command reaches the sheets/slides registry builtins through their own declared command id
- Verify: activate_command reaches the sheets/slides registry builtins through their own declared command id
   - Expected: host.activate_command("sheets.function.double") equals `1`
   - Expected: host.activate_command("slides.layout.titleDiagram") equals `1`
   - Expected: host.is_active("sheets-function-registry-demo") is true
   - Expected: host.is_active("slides-layout-registry-demo") is true
   - Expected: sheet_function_registry_has("DOUBLE") is true
   - Expected: slide_layout_registry_has("title_diagram") is true
   - Expected: host.activate_command("sheets.function.double") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("activate_command reaches the sheets/slides registry builtins through their own declared command id")
step("Verify: activate_command reaches the sheets/slides registry builtins through their own declared command id")
sheet_function_registry_reset()
slide_layout_registry_reset()
val host = extension_host_with_builtins_indexed()
expect(host.activate_command("sheets.function.double")).to_equal(1)
expect(host.activate_command("slides.layout.titleDiagram")).to_equal(1)
expect(host.is_active("sheets-function-registry-demo")).to_equal(true)
expect(host.is_active("slides-layout-registry-demo")).to_equal(true)
expect(sheet_function_registry_has("DOUBLE")).to_equal(true)
expect(slide_layout_registry_has("title_diagram")).to_equal(true)
# Idempotent: nothing left to activate the second time.
expect(host.activate_command("sheets.function.double")).to_equal(0)
```

</details>

#### a lazily-reachable builtin runs its hook only once its own event fires

- a lazily-reachable builtin runs its hook only once its own event fires
- Verify: a lazily-reachable builtin runs its hook only once its own event fires
   - Expected: host.activate_language("markdown") equals `1`
   - Expected: host.is_active("sheets-function-registry-demo") is false
   - Expected: sheet_function_registry_has("DOUBLE") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a lazily-reachable builtin runs its hook only once its own event fires")
step("Verify: a lazily-reachable builtin runs its hook only once its own event fires")
sheet_function_registry_reset()
val host = extension_host_with_builtins_indexed()
# Activating an unrelated language must not wake the sheets builtin.
expect(host.activate_language("markdown")).to_equal(1)
expect(host.is_active("sheets-function-registry-demo")).to_equal(false)
expect(sheet_function_registry_has("DOUBLE")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-EDITOR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `85bd1c4b2795f28782939ec34ec55ec695fe7d5abfef0eeca4b6a37d62006395`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85bd1c4b2795f28782939ec34ec55ec695fe7d5abfef0eeca4b6a37d62006395`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85bd1c4b2795f28782939ec34ec55ec695fe7d5abfef0eeca4b6a37d62006395`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/editor/extensions/activation_hook_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/extensions/activation_hook_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/extensions/activation_hook_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/extensions/activation_hook_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/extensions/activation_hook_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/extensions/activation_hook_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not run the hook before activation, then runs it exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/activation_hook_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not re-run the hook across a deactivate/activate cycle (guard against re-activation)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/extensions/activation_hook_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an Err hook becomes a diagnostic and does not crash the host; the extension still activates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
