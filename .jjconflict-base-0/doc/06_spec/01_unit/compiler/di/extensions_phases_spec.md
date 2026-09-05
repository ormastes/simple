# Extensions Phases Specification

> Tests covering Extensions: Phase 1 - Basic API, Extensions: Phase 2 - Integration, Extensions: Phase 3 - System behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extensions Phases Specification

## Scenarios

### Extensions: Phase 1 - Basic API

#### container construction

#### creates empty extensions container

- creates empty extensions container
   - Expected: ext.has("Anything") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates empty extensions container")
val ext = make_ext()
expect(ext.has("Anything")).to_equal(false)
```

</details>

#### starts with no bindings

- starts with no bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("starts with no bindings")
val ext = make_ext()
val result = ext.resolve_or("Missing", nil)
expect(result).to_be_nil()
```

</details>

#### profile is set correctly

- profile is set correctly
   - Expected: ext.profile equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("profile is set correctly")
val ext = make_ext()
expect(ext.profile).to_equal("dev")
```

</details>

#### locked is false by default

- locked is false by default
   - Expected: ext.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("locked is false by default")
val ext = make_ext()
expect(ext.locked).to_equal(false)
```

</details>

#### bind_instance operations

#### registers a text value

- registers a text value
   - Expected: ext.has("MyPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers a text value")
val ext = make_ext()
ext.bind_instance("MyPlugin", "plugin-v1")
expect(ext.has("MyPlugin")).to_equal(true)
```

</details>

#### resolves a registered text value

- resolves a registered text value
   - Expected: result equals `file-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a registered text value")
val ext = make_ext()
ext.bind_instance("Logger", "file-logger")
val result = ext.resolve("Logger")
expect(result).to_equal("file-logger")
```

</details>

#### registers an integer value

- registers an integer value
   - Expected: result equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers an integer value")
val ext = make_ext()
ext.bind_instance("MaxWorkers", 8)
val result = ext.resolve("MaxWorkers")
expect(result).to_equal(8)
```

</details>

#### registers a boolean value

- registers a boolean value
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers a boolean value")
val ext = make_ext()
ext.bind_instance("DebugMode", true)
val result = ext.resolve("DebugMode")
expect(result).to_equal(true)
```

</details>

#### resolve_or operations

#### returns nil for unregistered name

- returns nil for unregistered name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns nil for unregistered name")
val ext = make_ext()
val result = ext.resolve_or("NotHere", nil)
expect(result).to_be_nil()
```

</details>

#### returns default text for unregistered name

- returns default text for unregistered name
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns default text for unregistered name")
val ext = make_ext()
val result = ext.resolve_or("NotHere", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### returns registered value when present

- returns registered value when present
   - Expected: result equals `profiler-v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns registered value when present")
val ext = make_ext()
ext.bind_instance("Profiler", "profiler-v2")
val result = ext.resolve_or("Profiler", "default")
expect(result).to_equal("profiler-v2")
```

</details>

#### has operations

#### has returns false for unregistered

- has returns false for unregistered
   - Expected: ext.has("X") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has returns false for unregistered")
val ext = make_ext()
expect(ext.has("X")).to_equal(false)
```

</details>

#### has returns true for registered

- has returns true for registered
   - Expected: ext.has("X") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has returns true for registered")
val ext = make_ext()
ext.bind_instance("X", 1)
expect(ext.has("X")).to_equal(true)
```

</details>

### Extensions: Phase 2 - Integration

#### multiple plugins

#### registers two plugins independently

- registers two plugins independently
   - Expected: ext.has("PluginA") is true
   - Expected: ext.has("PluginB") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers two plugins independently")
val ext = make_ext()
ext.bind_instance("PluginA", "a")
ext.bind_instance("PluginB", "b")
expect(ext.has("PluginA")).to_equal(true)
expect(ext.has("PluginB")).to_equal(true)
```

</details>

#### resolves two plugins independently

- resolves two plugins independently
   - Expected: a equals `value-a`
   - Expected: b equals `value-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves two plugins independently")
val ext = make_ext()
ext.bind_instance("PluginA", "value-a")
ext.bind_instance("PluginB", "value-b")
val a = ext.resolve("PluginA")
val b = ext.resolve("PluginB")
expect(a).to_equal("value-a")
expect(b).to_equal("value-b")
```

</details>

#### registering one plugin does not affect another

- registering one plugin does not affect another


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registering one plugin does not affect another")
val ext = make_ext()
ext.bind_instance("PluginX", "x-value")
val other = ext.resolve_or("PluginY", nil)
expect(other).to_be_nil()
```

</details>

#### three plugins all registered correctly

- three plugins all registered correctly
   - Expected: ext.resolve("A") equals `alpha`
   - Expected: ext.resolve("B") equals `beta`
   - Expected: ext.resolve("C") equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("three plugins all registered correctly")
val ext = make_ext()
ext.bind_instance("A", "alpha")
ext.bind_instance("B", "beta")
ext.bind_instance("C", "gamma")
expect(ext.resolve("A")).to_equal("alpha")
expect(ext.resolve("B")).to_equal("beta")
expect(ext.resolve("C")).to_equal("gamma")
```

</details>

#### factory-based binding

#### bind factory creates value on resolve

- bind factory creates value on resolve
   - Expected: ext.has("LazyPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bind factory creates value on resolve")
val ext = make_ext()
ext.bind("LazyPlugin", fn(): "lazy-value")
expect(ext.has("LazyPlugin")).to_equal(true)
```

</details>

#### bind factory resolves to returned value

- bind factory resolves to returned value
   - Expected: result equals `created-on-demand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bind factory resolves to returned value")
val ext = make_ext()
ext.bind("Created", fn(): "created-on-demand")
val result = ext.resolve("Created")
expect(result).to_equal("created-on-demand")
```

</details>

#### factory and instance bindings coexist

- factory and instance bindings coexist
   - Expected: ext.resolve("Lazy") equals `lazy`
   - Expected: ext.resolve("Eager") equals `eager`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("factory and instance bindings coexist")
val ext = make_ext()
ext.bind("Lazy", fn(): "lazy")
ext.bind_instance("Eager", "eager")
expect(ext.resolve("Lazy")).to_equal("lazy")
expect(ext.resolve("Eager")).to_equal("eager")
```

</details>

#### extensions does not contain typed backend

#### backend is not in extensions by default

- backend is not in extensions by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backend is not in extensions by default")
val ext = make_ext()
val result = ext.resolve_or("Backend", nil)
expect(result).to_be_nil()
```

</details>

#### extensions starts clean for plugin use

- extensions starts clean for plugin use
   - Expected: ext.has("Backend") is false
   - Expected: ext.has("Logger") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extensions starts clean for plugin use")
val ext = make_ext()
expect(ext.has("Backend")).to_equal(false)
expect(ext.has("Logger")).to_equal(false)
```

</details>

### Extensions: Phase 3 - System behavior

#### lock protects extensions

#### is_locked is false initially

- is_locked is false initially
   - Expected: ext.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is_locked is false initially")
val ext = make_ext()
expect(ext.is_locked()).to_equal(false)
```

</details>

#### lock sets is_locked to true

- lock sets is_locked to true
   - Expected: ext.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lock sets is_locked to true")
val ext = make_ext()
ext.lock()
expect(ext.is_locked()).to_equal(true)
```

</details>

#### locked container rejects bind_instance

- locked container rejects bind_instance
   - Expected: ext.has("LockedPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("locked container rejects bind_instance")
val ext = make_ext()
ext.lock()
ext.bind_instance("LockedPlugin", "blocked")
expect(ext.has("LockedPlugin")).to_equal(false)
```

</details>

#### locked container rejects bind factory

- locked container rejects bind factory
   - Expected: ext.has("Blocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("locked container rejects bind factory")
val ext = make_ext()
ext.lock()
ext.bind("Blocked", fn(): "never")
expect(ext.has("Blocked")).to_equal(false)
```

</details>

#### unlock allows registration again

- unlock allows registration again
   - Expected: ext.has("Pre") is false
   - Expected: ext.has("Pre") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unlock allows registration again")
val ext = make_ext()
ext.lock()
ext.bind_instance("Pre", "v1")
expect(ext.has("Pre")).to_equal(false)
ext.unlock()
ext.bind_instance("Pre", "v1")
expect(ext.has("Pre")).to_equal(true)
```

</details>

#### pre-lock bindings still resolvable after lock

- pre-lock bindings still resolvable after lock
   - Expected: result equals `core-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pre-lock bindings still resolvable after lock")
val ext = make_ext()
ext.bind_instance("Core", "core-plugin")
ext.lock()
val result = ext.resolve("Core")
expect(result).to_equal("core-plugin")
```

</details>

#### resolve_or with defaults

#### locked container uses resolve_or for missing

- locked container uses resolve_or for missing
   - Expected: result equals `default-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("locked container uses resolve_or for missing")
val ext = make_ext()
ext.lock()
val result = ext.resolve_or("Missing", "default-plugin")
expect(result).to_equal("default-plugin")
```

</details>

#### resolve_or returns nil default correctly

- resolve_or returns nil default correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolve_or returns nil default correctly")
val ext = make_ext()
val result = ext.resolve_or("NoPlugin", nil)
expect(result).to_be_nil()
```

</details>

#### edge cases

#### empty name resolves to default

- empty name resolves to default
   - Expected: result equals `empty-default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("empty name resolves to default")
val ext = make_ext()
val result = ext.resolve_or("", "empty-default")
expect(result).to_equal("empty-default")
```

</details>

#### overwrite binding replaces old value

- overwrite binding replaces old value
   - Expected: result equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("overwrite binding replaces old value")
val ext = make_ext()
ext.bind_instance("Plugin", "v1")
ext.bind_instance("Plugin", "v2")
val result = ext.resolve("Plugin")
expect(result).to_equal("v2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/extensions_phases_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Extensions: Phase 1 - Basic API, Extensions: Phase 2 - Integration, Extensions: Phase 3 - System behavior.
- Extensions: Phase 1 - Basic API
- Extensions: Phase 2 - Integration
- Extensions: Phase 3 - System behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a63e6c99bb8a96ad7ad8647d3a487a23ae1f03c9a795f223110ecc656a1de30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a63e6c99bb8a96ad7ad8647d3a487a23ae1f03c9a795f223110ecc656a1de30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a63e6c99bb8a96ad7ad8647d3a487a23ae1f03c9a795f223110ecc656a1de30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/di/extensions_phases_spec.spl
mirror: doc/06_spec/01_unit/compiler/di/extensions_phases_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/di/extensions_phases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/di/extensions_phases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/di/extensions_phases_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/di/extensions_phases_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty extensions container' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/di/extensions_phases_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with no bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/di/extensions_phases_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'profile is set correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
