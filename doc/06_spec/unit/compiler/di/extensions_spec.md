# Extensions Specification

> Tests covering Extensions container: plugin registration, Extensions container: lock behavior, Extensions container: separation of concerns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extensions Specification

## Scenarios

### Extensions container: plugin registration

#### registers a plugin by name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers a plugin by name
   - Expected: ext.has("Profiler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a plugin by name")
val ext = make_extensions()
ext.bind_instance("Profiler", "profiler-v1")
expect(ext.has("Profiler")).to_equal(true)
```

</details>

#### resolves a registered plugin

- resolves a registered plugin
   - Expected: result equals `fmt-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a registered plugin")
val ext = make_extensions()
ext.bind_instance("Formatter", "fmt-plugin")
val result = ext.resolve("Formatter")
expect(result).to_equal("fmt-plugin")
```

</details>

#### returns nil for unregistered plugin via resolve_or

- returns nil for unregistered plugin via resolve_or


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unregistered plugin via resolve_or")
val ext = make_extensions()
val result = ext.resolve_or("MissingPlugin", nil)
expect(result).to_be_nil()
```

</details>

#### returns default for unregistered plugin via resolve_or

- returns default for unregistered plugin via resolve_or
   - Expected: result equals `default-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default for unregistered plugin via resolve_or")
val ext = make_extensions()
val result = ext.resolve_or("MissingPlugin", "default-value")
expect(result).to_equal("default-value")
```

</details>

#### registers multiple plugins independently

- registers multiple plugins independently
   - Expected: ext.has("PluginA") is true
   - Expected: ext.has("PluginB") is true
   - Expected: ext.resolve("PluginA") equals `a`
   - Expected: ext.resolve("PluginB") equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers multiple plugins independently")
val ext = make_extensions()
ext.bind_instance("PluginA", "a")
ext.bind_instance("PluginB", "b")
expect(ext.has("PluginA")).to_equal(true)
expect(ext.has("PluginB")).to_equal(true)
expect(ext.resolve("PluginA")).to_equal("a")
expect(ext.resolve("PluginB")).to_equal("b")
```

</details>

#### registers numeric plugin values

- registers numeric plugin values
   - Expected: result equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers numeric plugin values")
val ext = make_extensions()
ext.bind_instance("MaxWorkers", 4)
val result = ext.resolve("MaxWorkers")
expect(result).to_equal(4)
```

</details>

### Extensions container: lock behavior

#### blocks registration when locked

- blocks registration when locked
   - Expected: ext.has("LockedPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks registration when locked")
val ext = make_extensions()
ext.lock()
ext.bind_instance("LockedPlugin", "should-not-register")
expect(ext.has("LockedPlugin")).to_equal(false)
```

</details>

#### allows registration after unlock

- allows registration after unlock
   - Expected: ext.has("Temp") is false
   - Expected: ext.has("Temp") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows registration after unlock")
val ext = make_extensions()
ext.lock()
ext.bind_instance("Temp", "v1")
expect(ext.has("Temp")).to_equal(false)

ext.unlock()
ext.bind_instance("Temp", "v1")
expect(ext.has("Temp")).to_equal(true)
```

</details>

#### resolve still works when locked

- resolve still works when locked
   - Expected: result equals `log-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve still works when locked")
val ext = make_extensions()
ext.bind_instance("Logger", "log-plugin")
ext.lock()
val result = ext.resolve("Logger")
expect(result).to_equal("log-plugin")
```

</details>

#### is_locked reflects lock state

- is_locked reflects lock state
   - Expected: ext.is_locked() is false
   - Expected: ext.is_locked() is true
   - Expected: ext.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_locked reflects lock state")
val ext = make_extensions()
expect(ext.is_locked()).to_equal(false)
ext.lock()
expect(ext.is_locked()).to_equal(true)
ext.unlock()
expect(ext.is_locked()).to_equal(false)
```

</details>

### Extensions container: separation of concerns

#### extensions container starts empty

- extensions container starts empty
   - Expected: ext.has("Backend") is false
   - Expected: ext.has("Logger") is false
   - Expected: ext.has("AnyPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extensions container starts empty")
val ext = make_extensions()
expect(ext.has("Backend")).to_equal(false)
expect(ext.has("Logger")).to_equal(false)
expect(ext.has("AnyPlugin")).to_equal(false)
```

</details>

#### typed backend field is separate from extensions

- typed backend field is separate from extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("typed backend field is separate from extensions")
# Verify extensions does NOT hold the backend (typed field does)
val ext = make_extensions()
val backend_in_ext = ext.resolve_or("Backend", nil)
expect(backend_in_ext).to_be_nil()
```

</details>

#### plugin registration does not affect other plugins

- plugin registration does not affect other plugins
   - Expected: x_val equals `x-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plugin registration does not affect other plugins")
val ext = make_extensions()
ext.bind_instance("PluginX", "x-value")
val other = ext.resolve_or("PluginY", nil)
expect(other).to_be_nil()
val x_val = ext.resolve("PluginX")
expect(x_val).to_equal("x-value")
```

</details>

#### factory-bound extension resolves lazily

- factory-bound extension resolves lazily
   - Expected: ext.has("LazyPlugin") is true
   - Expected: result equals `lazy-created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("factory-bound extension resolves lazily")
val ext = make_extensions()
ext.bind("LazyPlugin", fn(): "lazy-created")
expect(ext.has("LazyPlugin")).to_equal(true)
val result = ext.resolve("LazyPlugin")
expect(result).to_equal("lazy-created")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/di/extensions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Extensions container: plugin registration, Extensions container: lock behavior, Extensions container: separation of concerns.
- Extensions container: plugin registration
- Extensions container: lock behavior
- Extensions container: separation of concerns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65dcc676effb3cd21e16b41c8a39a5a750be48fea8eeefca7032a9e2c4006146`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65dcc676effb3cd21e16b41c8a39a5a750be48fea8eeefca7032a9e2c4006146`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65dcc676effb3cd21e16b41c8a39a5a750be48fea8eeefca7032a9e2c4006146`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/di/extensions_spec.spl
mirror: doc/06_spec/unit/compiler/di/extensions_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/di/extensions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/di/extensions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/di/extensions_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/di/extensions_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers a plugin by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/di/extensions_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a registered plugin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/di/extensions_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for unregistered plugin via resolve_or' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
