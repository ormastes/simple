# Di Composition System Specification

> <details>

<!-- sdn-diagram:id=di_composition_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_composition_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_composition_system_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_composition_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Composition System Specification

## Scenarios

### DI Composition System: Features 1+2 - BackendPort in CompilerServices

#### CompilerServices contains a BackendPort as one of 9 typed ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.backend.name).to_equal("noop-backend")
expect(services.lexer.name).to_equal("noop-lexer")
expect(services.parser.name).to_equal("noop-parser")
```

</details>

#### BackendPort fn-fields are callable through CompilerServices

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val jit_f = backend.supports_jit_fn
val triple_f = backend.target_triple_fn
expect(jit_f()).to_equal(false)
expect(triple_f()).to_equal("noop")
```

</details>

#### all 9 ports are wired and callable end-to-end

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val src = "fn main(): print 1"
val module_name = "main"

val lf = svc.lexer.tokenize_fn
val tokens = lf(src)
expect(tokens.len()).to_equal(0)

val pf = svc.parser.parse_fn
val parse_errs = pf(tokens, src)
expect(parse_errs.len()).to_equal(0)

val df = svc.desugarer.desugar_fn
val desugared = df(src)
expect(desugared).to_equal(src)

val cf = svc.type_checker.check_fn
val type_errs = cf(module_name)
expect(type_errs.len()).to_equal(0)

val hf = svc.hir_lowerer.lower_fn
val hir_errs = hf(module_name)
expect(hir_errs.len()).to_equal(0)

val mf = svc.mir_lowerer.lower_fn
val mir_errs = mf(module_name)
expect(mir_errs.len()).to_equal(0)

val bf = svc.backend.supports_jit_fn
expect(bf()).to_equal(false)
```

</details>

#### backend port in services has distinct identity from other ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
expect(svc.backend.name).to_equal("noop-backend")
expect(svc.logger.name).to_equal("noop-logger")
expect(svc.module_loader.name).to_equal("noop-module-loader")
```

</details>

### DI Composition System: Features 5+9 - Extensions with Lock

#### extensions container registers plugins before lock

1. ext bind instance
2. ext bind instance
   - Expected: ext.has("Profiler") is true
   - Expected: ext.has("Formatter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_di()
ext.bind_instance("Profiler", "profiler-v1")
ext.bind_instance("Formatter", "fmt-v1")
expect(ext.has("Profiler")).to_equal(true)
expect(ext.has("Formatter")).to_equal(true)
```

</details>

#### lock prevents new plugin registration

1. ext bind instance
2. ext lock
3. ext bind instance
   - Expected: ext.has("Profiler") is true
   - Expected: ext.has("Injected") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_di()
ext.bind_instance("Profiler", "profiler-v1")
ext.lock()
ext.bind_instance("Injected", "should-not-register")
expect(ext.has("Profiler")).to_equal(true)
expect(ext.has("Injected")).to_equal(false)
```

</details>

#### pre-lock plugins remain accessible after lock

1. ext bind instance
2. ext bind instance
3. ext lock
   - Expected: ext.resolve("Core") equals `core-plugin`
   - Expected: ext.resolve("Logger") equals `log-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_di()
ext.bind_instance("Core", "core-plugin")
ext.bind_instance("Logger", "log-plugin")
ext.lock()
expect(ext.resolve("Core")).to_equal("core-plugin")
expect(ext.resolve("Logger")).to_equal("log-plugin")
```

</details>

#### unlock allows new plugins after lock-unlock cycle

1. ext bind instance
2. ext lock
3. ext bind instance
4. ext unlock
5. ext bind instance
   - Expected: ext.has("V1") is true
   - Expected: ext.has("V2") is true
   - Expected: ext.resolve("V2") equals `allowed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_di()
ext.bind_instance("V1", "first")
ext.lock()
ext.bind_instance("V2", "blocked")
ext.unlock()
ext.bind_instance("V2", "allowed")
expect(ext.has("V1")).to_equal(true)
expect(ext.has("V2")).to_equal(true)
expect(ext.resolve("V2")).to_equal("allowed")
```

</details>

#### resolve_or works regardless of lock state

1. ext bind instance
   - Expected: pre_lock equals `known-value`
2. ext lock
   - Expected: post_lock equals `known-value`
   - Expected: missing equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_di()
ext.bind_instance("Known", "known-value")
val pre_lock = ext.resolve_or("Known", "default")
expect(pre_lock).to_equal("known-value")
ext.lock()
val post_lock = ext.resolve_or("Known", "default")
expect(post_lock).to_equal("known-value")
val missing = ext.resolve_or("Unknown", "fallback")
expect(missing).to_equal("fallback")
```

</details>

### DI Composition System: Features 1+2+5+9 - Full integration

#### services pipeline and extension container are independent

1. ext bind instance
   - Expected: backend_name equals `noop-backend`
   - Expected: ext.has("ExtraPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val ext = make_di()

ext.bind_instance("ExtraPlugin", "extra-v1")

val backend_name = svc.backend.name
expect(backend_name).to_equal("noop-backend")
expect(ext.has("ExtraPlugin")).to_equal(true)
expect(ext.resolve_or("Backend", nil)).to_be_nil()
```

</details>

#### locking extensions does not affect CompilerServices

1. ext lock
   - Expected: lexer_name equals `noop-lexer`
   - Expected: backend_name equals `noop-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val ext = make_di()
ext.lock()

val lexer_name = svc.lexer.name
val backend_name = svc.backend.name
expect(lexer_name).to_equal("noop-lexer")
expect(backend_name).to_equal("noop-backend")
```

</details>

#### pipeline ports remain callable while extensions are locked

1. ext bind instance
2. ext lock
   - Expected: result equals `source code`
   - Expected: ext.resolve("Plugin") equals `v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val ext = make_di()
ext.bind_instance("Plugin", "v1")
ext.lock()

val df = svc.desugarer.desugar_fn
val result = df("source code")
expect(result).to_equal("source code")
expect(ext.resolve("Plugin")).to_equal("v1")
```

</details>

#### extensions and pipeline together in realistic scenario

1. ext bind instance
2. ext bind instance
   - Expected: tokens.len() equals `0`
   - Expected: desugared equals `src`
   - Expected: telemetry equals `otel-v2`
   - Expected: flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val ext = make_di()

ext.bind_instance("Telemetry", "otel-v2")
ext.bind_instance("FeatureFlag", true)

val src = "fn greet(): print 1"
val lf = svc.lexer.tokenize_fn
val tokens = lf(src)
expect(tokens.len()).to_equal(0)

val df = svc.desugarer.desugar_fn
val desugared = df(src)
expect(desugared).to_equal(src)

val telemetry = ext.resolve("Telemetry")
expect(telemetry).to_equal("otel-v2")

val flag = ext.resolve("FeatureFlag")
expect(flag).to_equal(true)
```

</details>

#### di_is_system_test_locked works independently of extension lock

1. rt env set
2. rt env set
3. ext lock
   - Expected: ext.is_locked() is true
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
val ext = make_di()
ext.lock()

expect(ext.is_locked()).to_equal(true)
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### env-var lock and explicit lock are independent mechanisms

1. rt env set
2. ext1 lock
3. ext1 bind instance
   - Expected: ext1.has("Blocked") is false
4. ext2 bind instance
   - Expected: ext2.has("Allowed") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
val ext1 = make_di()
ext1.lock()

val ext2 = make_di()

ext1.bind_instance("Blocked", "blocked")
expect(ext1.has("Blocked")).to_equal(false)

ext2.bind_instance("Allowed", "allowed")
expect(ext2.has("Allowed")).to_equal(true)
```

</details>

#### complete DI composition: typed ports + extensions + lock

1. ext bind instance
2. ext bind instance
   - Expected: jit_f() is false
   - Expected: triple_f() equals `noop`
3. ext lock
   - Expected: ext.resolve("Logger") equals `structured-logger`
   - Expected: ext.resolve("MetricsCollector") equals `prometheus-v2`
4. ext bind instance
   - Expected: ext.has("PostLockPlugin") is false
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = create_default_services()
val ext = make_di()

ext.bind_instance("Logger", "structured-logger")
ext.bind_instance("MetricsCollector", "prometheus-v2")

val backend = svc.backend
val jit_f = backend.supports_jit_fn
val triple_f = backend.target_triple_fn

expect(jit_f()).to_equal(false)
expect(triple_f()).to_equal("noop")

ext.lock()

expect(ext.resolve("Logger")).to_equal("structured-logger")
expect(ext.resolve("MetricsCollector")).to_equal("prometheus-v2")

ext.bind_instance("PostLockPlugin", "rejected")
expect(ext.has("PostLockPlugin")).to_equal(false)

val lf = svc.module_loader.load_fn
val content = lf("/src/main.spl")
expect(content).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/di_composition_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DI Composition System: Features 1+2 - BackendPort in CompilerServices
- DI Composition System: Features 5+9 - Extensions with Lock
- DI Composition System: Features 1+2+5+9 - Full integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
