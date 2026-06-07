# Pipeline Integration Specification

> <details>

<!-- sdn-diagram:id=pipeline_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipeline_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipeline_integration_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipeline_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pipeline Integration Specification

## Scenarios

### CompilationEventPort noop

#### creates noop event port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = create_noop_event_port()
expect(port.name).to_equal("noop-events")
```

</details>

#### noop callbacks do not crash

1. f1
2. f2
3. f3
4. f4
5. f5
   - Expected: port.name equals `noop-events`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = create_noop_event_port()
val f1 = port.on_lex_complete_fn
f1(100)
val f2 = port.on_parse_complete_fn
f2(50)
val f3 = port.on_hir_complete_fn
f3(50)
val f4 = port.on_mir_complete_fn
f4(50)
val f5 = port.on_backend_complete_fn
f5(true)
expect(port.name).to_equal("noop-events")
```

</details>

### Custom event port

#### tracks stage count

1. fp
2. fh
   - Expected: _test_prof_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_prof_count = 0
_test_prof_last = ""
val port = CompilationEventPort(
    name: "test-profiler",
    on_lex_complete_fn: _test_prof_i64,
    on_parse_complete_fn: _test_prof_parse,
    on_desugar_complete_fn: _test_prof_i64,
    on_type_check_complete_fn: _test_prof_two,
    on_hir_complete_fn: _test_prof_hir,
    on_mir_complete_fn: _test_prof_mir,
    on_backend_complete_fn: _test_prof_bool
)
val fp = port.on_parse_complete_fn
fp(10)
val fh = port.on_hir_complete_fn
fh(10)
expect(_test_prof_count).to_equal(2)
```

</details>

#### tracks last stage

1. fp
2. fh
3. fm
   - Expected: _test_prof_last equals `mir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_prof_count = 0
_test_prof_last = ""
val port = CompilationEventPort(
    name: "test-profiler",
    on_lex_complete_fn: _test_prof_i64,
    on_parse_complete_fn: _test_prof_parse,
    on_desugar_complete_fn: _test_prof_i64,
    on_type_check_complete_fn: _test_prof_two,
    on_hir_complete_fn: _test_prof_hir,
    on_mir_complete_fn: _test_prof_mir,
    on_backend_complete_fn: _test_prof_bool
)
val fp = port.on_parse_complete_fn
fp(10)
val fh = port.on_hir_complete_fn
fh(10)
val fm = port.on_mir_complete_fn
fm(10)
expect(_test_prof_last).to_equal("mir")
```

</details>

#### tracks all seven stages

1. f1
2. f2
3. f3
4. f4
5. f5
6. f6
7. f7
   - Expected: _test_prof_count equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_prof_count = 0
val port = CompilationEventPort(
    name: "test-profiler",
    on_lex_complete_fn: _test_prof_i64,
    on_parse_complete_fn: _test_prof_parse,
    on_desugar_complete_fn: _test_prof_i64,
    on_type_check_complete_fn: _test_prof_two,
    on_hir_complete_fn: _test_prof_hir,
    on_mir_complete_fn: _test_prof_mir,
    on_backend_complete_fn: _test_prof_bool
)
val f1 = port.on_lex_complete_fn
f1(100)
val f2 = port.on_parse_complete_fn
f2(50)
val f3 = port.on_desugar_complete_fn
f3(50)
val f4 = port.on_type_check_complete_fn
f4(0, 200)
val f5 = port.on_hir_complete_fn
f5(50)
val f6 = port.on_mir_complete_fn
f6(50)
val f7 = port.on_backend_complete_fn
f7(true)
expect(_test_prof_count).to_equal(7)
```

</details>

### ModuleStoragePort file-backed

#### creates file storage

1. fn  read file
   - Expected: storage.name equals `file-storage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn _read_file(path: text) -> text: rt_file_read_text(path) ?? ""
val storage = ModuleStoragePort(name: "file-storage", read_source_fn: _read_file)
expect(storage.name).to_equal("file-storage")
```

</details>

#### reads existing file

1. fn  read file2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn _read_file2(path: text) -> text: rt_file_read_text(path) ?? ""
val storage = ModuleStoragePort(name: "file-storage", read_source_fn: _read_file2)
val reader = storage.read_source_fn
val content = reader("src/app/cli/main.spl")
expect(content.len()).to_be_greater_than(0)
```

</details>

#### returns empty for missing file

1. fn  read file3
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn _read_file3(path: text) -> text: rt_file_read_text(path) ?? ""
val storage = ModuleStoragePort(name: "file-storage", read_source_fn: _read_file3)
val reader = storage.read_source_fn
val content = reader("nonexistent_xyz.spl")
expect(content).to_equal("")
```

</details>

### ModuleStoragePort memory-backed

#### creates memory storage

1. fn  test read
   - Expected: storage.name equals `memory-storage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn _test_read(path: text) -> text: ""
val storage = ModuleStoragePort(name: "memory-storage", read_source_fn: _test_read)
expect(storage.name).to_equal("memory-storage")
```

</details>

### LoggerPort

#### creates noop logger

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger = LoggerPort(
    name: "test-logger",
    level: 0
)
expect(logger.name).to_equal("test-logger")
```

</details>

#### noop logger has level field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger = LoggerPort(
    name: "silent",
    level: 0
)
expect(logger.level).to_equal(0)
```

</details>

### CompilerServices

#### creates default services

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.lexer.name).to_equal("noop-lexer")
expect(services.parser.name).to_equal("noop-parser")
expect(services.backend.name).to_equal("noop-backend")
expect(services.logger.name).to_equal("noop-logger")
expect(services.module_loader.name).to_equal("noop-module-loader")
```

</details>

#### all ports have names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.desugarer.name).to_equal("noop-desugarer")
expect(services.type_checker.name).to_equal("noop-type-checker")
expect(services.hir_lowerer.name).to_equal("noop-hir-lowerer")
expect(services.mir_lowerer.name).to_equal("noop-mir-lowerer")
```

</details>

### CachePort noop

#### creates noop cache port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = create_noop_cache_port()
expect(cache.name).to_equal("noop-cache")
```

</details>

#### noop cache always misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = create_noop_cache_port()
val check = cache.check_fn
val status = check("key", "hash")
expect(status.is_fresh).to_equal(false)
```

</details>

#### noop cache stats are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = create_noop_cache_port()
val get_stats = cache.get_stats_fn
val stats = get_stats()
expect(stats.hits).to_equal(0)
expect(stats.misses).to_equal(0)
```

</details>

#### store does not crash

1. store
   - Expected: stats.stores equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = create_noop_cache_port()
val store = cache.store_fn
store("key", "hash", "data")
val get_stats = cache.get_stats_fn
val stats = get_stats()
expect(stats.stores).to_equal(0)
```

</details>

#### invalidate does not crash

1. inv
   - Expected: stats.invalidations equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = create_noop_cache_port()
val inv = cache.invalidate_fn
inv("key")
val get_stats = cache.get_stats_fn
val stats = get_stats()
expect(stats.invalidations).to_equal(0)
```

</details>

### CacheStats

#### stores hit and miss counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = CacheStats(hits: 8, misses: 2, stores: 0, invalidations: 0)
expect(stats.hits).to_equal(8)
expect(stats.misses).to_equal(2)
```

</details>

### MetricsPort noop

#### creates noop metrics port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = create_noop_metrics_port()
expect(metrics.name).to_equal("noop-metrics")
```

</details>

#### noop record does not crash

1. rc
2. rg
3. rt
   - Expected: gc("test") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = create_noop_metrics_port()
val rc = metrics.record_counter_fn
rc("test", 1)
val rg = metrics.record_gauge_fn
rg("test", 42)
val rt = metrics.record_timing_fn
rt("test", 100)
val gc = metrics.get_counter_fn
expect(gc("test")).to_equal(0)
```

</details>

#### noop get does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = create_noop_metrics_port()
val gc = metrics.get_counter_fn
expect(gc("test")).to_equal(0)
```

</details>

### MetricsPort custom

#### creates custom metrics port

1. fn  mc noop
2. fn  mc zero
   - Expected: metrics.name equals `test-metrics`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn _mc_noop(name: text, value: i64): ()
fn _mc_zero(name: text) -> i64: 0
val metrics = MetricsPort(
    name: "test-metrics",
    record_counter_fn: _mc_noop,
    record_gauge_fn: _mc_noop,
    record_timing_fn: _mc_noop,
    get_counter_fn: _mc_zero,
    get_gauge_fn: _mc_zero,
    get_timing_fn: _mc_zero
)
expect(metrics.name).to_equal("test-metrics")
```

</details>

### CompileContext MDSOC ports

#### creates context with event port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.event_port.name).to_equal("noop-events")
```

</details>

#### creates context with module storage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.module_storage.name).to_equal("file-module-storage")
```

</details>

#### creates context with logger port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.logger_port.name).to_equal("boot-log")
```

</details>

#### creates context with cache port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.cache_port.name).to_equal("noop-cache")
```

</details>

#### creates context with metrics port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.metrics_port.name).to_equal("noop-metrics")
```

</details>

### AopWeaver

#### creates weaver with disabled config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = WeavingConfig(enabled: false, before_advices: [], after_success_advices: [], after_error_advices: [], around_advices: [])
val logger = BootLogger(level: 0)
val weaver = AopWeaver(advices: [], config: config, logger: logger)
expect(weaver.config.enabled).to_equal(false)
```

</details>

#### weaves empty function list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = WeavingConfig(enabled: false, before_advices: [], after_success_advices: [], after_error_advices: [], around_advices: [])
val logger = BootLogger(level: 0)
val weaver = AopWeaver(advices: [], config: config, logger: logger)
val result = weaver.weave_mir_function("test_fn", "test_mod", [], [], [])
expect(result.advices_inserted).to_equal(0)
```

</details>

### CompilerServices real wiring

#### services backend matches context backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.services.backend.name).to_equal(ctx.backend.name)
```

</details>

#### services logger matches context logger port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.services.logger.name).to_equal("boot-log")
```

</details>

#### services module loader is real

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.services.module_loader.name).to_equal("file-loader")
```

</details>

#### services pipeline ports are noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
val ctx = CompileContext.create(opts)
expect(ctx.services.lexer.name).to_equal("noop-lexer")
expect(ctx.services.parser.name).to_equal("noop-parser")
expect(ctx.services.desugarer.name).to_equal("noop-desugarer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/pipeline_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CompilationEventPort noop
- Custom event port
- ModuleStoragePort file-backed
- ModuleStoragePort memory-backed
- LoggerPort
- CompilerServices
- CachePort noop
- CacheStats
- MetricsPort noop
- MetricsPort custom
- CompileContext MDSOC ports
- AopWeaver
- CompilerServices real wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
