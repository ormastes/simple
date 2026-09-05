# Di Extensions System Specification

> <details>

<!-- sdn-diagram:id=di_extensions_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_extensions_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_extensions_system_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_extensions_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Extensions System Specification

## Scenarios

### DI System: Extensions + Lock integration

#### CompileContext extensions starts empty and unlocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulates the extensions field created by CompileContext.create
val extensions = make_extensions()
expect(extensions.has("AnyPlugin")).to_equal(false)
expect(extensions.is_locked()).to_equal(false)
```

</details>

#### register plugins before lock (setup phase)

1. extensions bind instance
2. extensions bind instance
3. extensions bind instance
   - Expected: extensions.has("Profiler") is true
   - Expected: extensions.has("Formatter") is true
   - Expected: extensions.has("Linter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_extensions()
extensions.bind_instance("Profiler", "profiler-impl")
extensions.bind_instance("Formatter", "fmt-impl")
extensions.bind_instance("Linter", "lint-impl")
expect(extensions.has("Profiler")).to_equal(true)
expect(extensions.has("Formatter")).to_equal(true)
expect(extensions.has("Linter")).to_equal(true)
```

</details>

#### lock the container after setup

1. extensions bind instance
2. extensions lock
   - Expected: extensions.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_extensions()
extensions.bind_instance("Plugin", "plugin-v1")
extensions.lock()
expect(extensions.is_locked()).to_equal(true)
```

</details>

#### resolve plugins during compilation (locked)

1. extensions bind instance
2. extensions bind instance
3. extensions lock
   - Expected: profiler equals `profiler-impl`
   - Expected: formatter equals `fmt-impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_extensions()
extensions.bind_instance("Profiler", "profiler-impl")
extensions.bind_instance("Formatter", "fmt-impl")
extensions.lock()
val profiler = extensions.resolve("Profiler")
val formatter = extensions.resolve("Formatter")
expect(profiler).to_equal("profiler-impl")
expect(formatter).to_equal("fmt-impl")
```

</details>

#### locked extensions rejects new plugin registration

1. extensions bind instance
2. extensions lock
3. extensions bind instance
   - Expected: extensions.has("NewPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_extensions()
extensions.bind_instance("Plugin", "plugin-v1")
extensions.lock()
extensions.bind_instance("NewPlugin", "new-v1")
expect(extensions.has("NewPlugin")).to_equal(false)
```

</details>

#### extensions is separate from typed backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The typed backend is in CompileContext.backend (BackendPort)
# Extensions only holds plugins explicitly registered
val extensions = make_extensions()
val backend_result = extensions.resolve_or("Backend", nil)
expect(backend_result).to_be_nil()
```

</details>

#### factory-bound plugin resolves correctly when locked

1. extensions bind
2. extensions lock
   - Expected: result equals `analysis-result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_extensions()
extensions.bind("AnalysisPlugin", fn(): "analysis-result")
extensions.lock()
val result = extensions.resolve("AnalysisPlugin")
expect(result).to_equal("analysis-result")
```

</details>

#### full compilation plugin lifecycle

1. extensions bind instance
2. extensions bind instance
3. extensions bind
4. extensions lock
   - Expected: extensions.is_locked() is true
   - Expected: checker equals `type-checker-v2`
   - Expected: optimizer equals `optimizer-v1`
   - Expected: codegen equals `codegen-impl`
5. extensions bind instance
   - Expected: extensions.has("RuntimePlugin") is false
6. extensions unlock
   - Expected: extensions.is_locked() is false
7. extensions bind instance
   - Expected: extensions.has("PostPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Full lifecycle: setup -> lock -> use -> unlock -> teardown
val extensions = make_extensions()

# Setup phase: register plugins
extensions.bind_instance("TypeChecker", "type-checker-v2")
extensions.bind_instance("Optimizer", "optimizer-v1")
extensions.bind("CodeGen", fn(): "codegen-impl")

# Lock before compilation
extensions.lock()
expect(extensions.is_locked()).to_equal(true)

# Compilation phase: resolve plugins (read-only)
val checker = extensions.resolve("TypeChecker")
val optimizer = extensions.resolve("Optimizer")
val codegen = extensions.resolve("CodeGen")
expect(checker).to_equal("type-checker-v2")
expect(optimizer).to_equal("optimizer-v1")
expect(codegen).to_equal("codegen-impl")

# Locked: no new bindings during compilation
extensions.bind_instance("RuntimePlugin", "should-not-register")
expect(extensions.has("RuntimePlugin")).to_equal(false)

# Teardown / reconfiguration: unlock
extensions.unlock()
expect(extensions.is_locked()).to_equal(false)

# Can add new plugins after unlock
extensions.bind_instance("PostPlugin", "post-v1")
expect(extensions.has("PostPlugin")).to_equal(true)
```

</details>

#### di_is_system_test_locked returns false in non-system-test env

1. rt env set
2. rt env set
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
val result = di_is_system_test_locked()
expect(result).to_equal(false)
```

</details>

#### multiple independent extension containers do not interfere

1. ext1 bind instance
   - Expected: ext1_result equals `from-ext1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext1 = make_extensions()
val ext2 = make_extensions()
ext1.bind_instance("Plugin", "from-ext1")
val result = ext2.resolve_or("Plugin", nil)
expect(result).to_be_nil()
val ext1_result = ext1.resolve("Plugin")
expect(ext1_result).to_equal("from-ext1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/di_extensions_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DI System: Extensions + Lock integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
