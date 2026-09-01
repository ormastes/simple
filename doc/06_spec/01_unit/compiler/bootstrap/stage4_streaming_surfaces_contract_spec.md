# Stage4 Streaming Surfaces Contract Specification

> Tests covering Stage4 streaming surface ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Streaming Surfaces Contract Specification

## Scenarios

### Stage4 streaming surface ownership

#### keeps the complete module surface registry reference-owned

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the complete module surface registry reference-owned
   - Expected: surface does not contain `struct ModuleSurfacesByName:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the complete module surface registry reference-owned")
val surface = file_read(SURFACE)
expect(surface).to_contain("class ModuleSurfacesByName:")
expect(surface.contains("struct ModuleSurfacesByName:")).to_equal(false)
```

</details>

#### bounds source 11 and projects it through compact headers and a reference owner

- bounds source 11 and projects it through compact headers and a reference owner
   - Expected: source_11 does not contain `fn eval_expr(`
   - Expected: source_11 does not contain `fn eval_binop(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds source 11 and projects it through compact headers and a reference owner")
val parser_types = file_read(PARSER_TYPES)
val assembly = file_read(MODULE_ASSEMBLY)
val desugar = file_read(DESUGAR_ASYNC)
val surface = file_read(SURFACE)
val driver = file_read(SOURCE_PARSING)
val source_11 = file_read(SOURCE_11)
val source_11_expr = file_read(SOURCE_11_EXPR)
val source_11_binop = file_read(SOURCE_11_BINOP)
expect(source_11.len()).to_be_less_than(35000)
expect(source_11_expr.len()).to_be_less_than(30000)
expect(source_11_binop.len()).to_be_less_than(20000)
expect(source_11.contains("fn eval_expr(")).to_equal(false)
expect(source_11.contains("fn eval_binop(")).to_equal(false)
expect(source_11).to_contain("use compiler.backend.backend.interpreter_expr.*")
expect(source_11).to_contain("use compiler.backend.backend.interpreter_binop.*")
expect(source_11_expr).to_contain("fn eval_expr(")
expect(source_11_binop).to_contain("fn eval_binop(")
expect(parser_types).to_contain("function_headers: Dict<text, ParserFunctionHeader>")
expect(parser_types).to_contain("fn parser_function_header(function_: ParserFunction)")
expect(assembly).to_contain("function_headers[fn_.name] = parser_function_header(fn_)")
expect(assembly).to_contain("built_module.function_headers = function_headers")
expect(desugar).to_contain("function_headers: desugared_function_headers")
expect(surface).to_contain("class ModuleSurfaceParserOwner:")
expect(surface).to_contain("owner: ModuleSurfaceParserOwner")
expect(surface).to_contain("owner.value.function_headers.contains_key(name)")
expect(driver).to_contain("val module_owner = ModuleSurfaceParserOwner.new(module)")
expect(driver).to_contain("module_surface_from_owner(")
expect(driver).to_contain("log_module_surface_stage(source.path, \"parse-start\")")
expect(driver).to_contain("log_module_surface_stage(source.path, \"surface-done\")")
```

</details>

#### retains type aliases and required declaration carriers

- retains type aliases and required declaration carriers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains type aliases and required declaration carriers")
val surface = file_read(SURFACE)
val lowering = file_read(LOWERING)
expect(surface).to_contain("type_aliases: Dict<text, ModuleSurfaceTypeAlias>")
expect(surface).to_contain("for name in owner.value.type_aliases.keys():")
expect(surface).to_contain("default_methods: [Function]")
expect(surface).to_contain("variants: [Variant]")
expect(lowering).to_contain("if m.type_aliases.contains_key(name):")
expect(lowering).to_contain("keys = imported_mod.type_aliases.keys()")
```

</details>

#### requires every explicit Stage4 admission condition without a resource-profile gate

- requires every explicit Stage4 admission condition without a resource-profile gate
   - Expected: selector does not contain `ctx.options.low_memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires every explicit Stage4 admission condition without a resource-profile gate")
val driver = file_read(ORCHESTRATION)
val producer = file_read(PRODUCER)
val selector_start = driver.index_of("pub fn driver_streaming_surface_enabled")
val selector_end = driver.index_of("impl CompilerDriver:")
expect(selector_start).to_be_greater_than(0)
expect(selector_end).to_be_greater_than(selector_start)
val selector = driver.substring(selector_start, selector_end)
expect(selector).to_contain("ctx.options.mode == CompileMode.Aot")
expect(selector.contains("ctx.options.low_memory")).to_equal(false)
expect(selector).to_contain("SIMPLE_BOOTSTRAP")
expect(selector).to_contain("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE")
expect(selector).to_contain("SIMPLE_BOOTSTRAP_STAGE4")
expect(selector).to_contain("SIMPLE_STAGE4_STREAMING_SURFACES")
expect(selector).to_contain("SIMPLE_STAGE3_STREAMING_SURFACES")
expect(selector).to_contain("ctx.options.backend != \"vhdl\"")
expect(producer).to_contain("SIMPLE_BOOTSTRAP_LOW_MEMORY=1")
expect(producer).to_contain("SIMPLE_STAGE4_STREAMING_SURFACES=1")
expect(producer).to_contain("SIMPLE_STAGE3_STREAMING_SURFACES=1")
expect(producer).to_contain("SIMPLE_NATIVE_ARENA_DECLS=1")
expect(producer).to_contain("Stage 4 emitted stale flat-AST index diagnostics")
```

</details>

#### keeps structural streaming enabled for the unlimited incremental profile

- keeps structural streaming enabled for the unlimited incremental profile
   - Expected: producer does not contain `stage4_low_memory=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps structural streaming enabled for the unlimited incremental profile")
val producer = file_read(PRODUCER)
expect(producer).to_contain("execution_profile=incremental-unlimited")
expect(producer).to_contain("jobs=")
expect(producer).to_contain("host_cpus")
expect(producer).to_contain("--threads")
expect(producer).to_contain("selfhost_jobs")
expect(producer).to_contain("--low-memory")
expect(producer).to_contain("SIMPLE_BOOTSTRAP_LOW_MEMORY=1")
expect(producer.contains("stage4_low_memory=0")).to_equal(false)
```

</details>

#### keeps streaming opt-in with Stage3 and legacy Stage4 producers

- keeps streaming opt-in with Stage3 and legacy Stage4 producers


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps streaming opt-in with Stage3 and legacy Stage4 producers")
val driver = file_read(ORCHESTRATION)
val selector_start = driver.index_of("pub fn driver_streaming_surface_enabled")
val selector_end = driver.index_of("impl CompilerDriver:")
val selector = driver.substring(selector_start, selector_end)
expect(selector).to_contain("SIMPLE_STAGE3_STREAMING_SURFACES")
expect(selector).to_contain("SIMPLE_BOOTSTRAP_STAGE4")
expect(selector).to_contain("SIMPLE_STAGE4_STREAMING_SURFACES")
expect(selector).to_contain("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE")
expect(selector).to_contain("ctx.options.mode == CompileMode.Aot")
expect(selector).to_contain("ctx.options.backend != \"vhdl\"")
```

</details>

#### enables native declaration arenas in the Stage3 transcribed build

- enables native declaration arenas in the Stage3 transcribed build


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables native declaration arenas in the Stage3 transcribed build")
val producer = file_read(PRODUCER)
val hash_start = producer.index_of("stage3_build_args_sha256=$(")
val stage3_start = producer.index_of("# Stage 3: stage2 recompiles bootstrap_main.spl")
val stage3_end = producer.index_of("stage3_status=$?")
expect(hash_start).to_be_greater_than(0)
expect(stage3_start).to_be_greater_than(hash_start)
expect(stage3_end).to_be_greater_than(stage3_start)
val hash_block = producer.substring(hash_start, stage3_start)
val stage3_block = producer.substring(stage3_start, stage3_end)
expect(hash_block).to_contain("\"SIMPLE_STAGE3_STREAMING_SURFACES=1\"")
expect(stage3_block).to_contain("SIMPLE_STAGE3_STREAMING_SURFACES=1")
expect(hash_block).to_contain("\"MALLOC_ARENA_MAX=2\"")
expect(hash_block).to_contain("\"MALLOC_TRIM_THRESHOLD_=0\"")
expect(stage3_block).to_contain("MALLOC_ARENA_MAX=2")
expect(stage3_block).to_contain("MALLOC_TRIM_THRESHOLD_=0")
expect(hash_block).to_contain("\"SIMPLE_NATIVE_ARENA_DECLS=1\"")
expect(stage3_block).to_contain("SIMPLE_NATIVE_ARENA_DECLS=1")
```

</details>

#### promotes only the retained surface before reclaiming the rich module

- promotes only the retained surface before reclaiming the rich module
   - Expected: body does not contain `rt_transient_heap_promote(module)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("promotes only the retained surface before reclaiming the rich module")
val driver = file_read(SOURCE_PARSING)
val start = driver.index_of("me add_streaming_module_surface")
val end = driver.index_of("me parse_all_streaming_surfaces_impl")
val body = driver.substring(start, end)
val begin = body.index_of("rt_transient_array_scope_begin()")
val parse = body.index_of("parse_full_frontend(")
val owner = body.index_of("ModuleSurfaceParserOwner.new(module)")
val build = body.index_of("module_surface_from_owner(")
val surface_unwrap = body.index_of("surface_result.unwrap()")
val pause = body.index_of("rt_transient_array_scope_pause()")
val promote = body.index_of("module_surface_promote(")
val publish = body.index_of("builder.add_surface_canonical(")
val reclaim = body.last_index_of("driver_end_transient_parse_scope()")
expect(begin).to_be_greater_than(0)
expect(parse).to_be_greater_than(begin)
expect(owner).to_be_greater_than(parse)
expect(build).to_be_greater_than(owner)
expect(surface_unwrap).to_be_greater_than(build)
expect(pause).to_be_greater_than(surface_unwrap)
expect(promote).to_be_greater_than(pause)
expect(publish).to_be_greater_than(promote)
expect(reclaim).to_be_greater_than(publish)
expect(body.contains("rt_transient_heap_promote(module)")).to_equal(false)
```

</details>

#### walks retained graphs through raw struct allocations

- walks retained graphs through raw struct allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks retained graphs through raw struct allocations")
val runtime = file_read(RUNTIME)
val check = file_read(RUNTIME_CHECK)
val rust_runtime = file_read(RUST_RUNTIME)
val rust_memory = file_read(RUST_MEMORY)
expect(runtime).to_contain("RT_CORE_TRANSIENT_RAW")
expect(runtime).to_contain("rt_core_transient_raw_lookup(raw_ptr)")
expect(runtime).to_contain("offset + sizeof(int64_t) <= node.bytes")
expect(check).to_contain("tagged raw root promotes through collection and raw aggregate edges")
expect(check).to_contain("a second promotion of the retained graph succeeds")
expect(rust_runtime).to_contain("rt_transient_raw_words")
expect(rust_runtime).to_contain("reachable_raw")
expect(rust_memory).to_contain("rt_transient_raw_scope_end")
expect(rust_memory).to_contain("RT_TRANSIENT_RAW_OWNED_BIT")
```

</details>

#### ends a transient scope before replacing parser roots

- ends a transient scope before replacing parser roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends a transient scope before replacing parser roots")
val driver = file_read(SOURCE_PARSING)
val start = driver.index_of("fn driver_end_transient_parse_scope")
val end = driver.index_of("impl CompilerDriver:")
val body = driver.substring(start, end)
val lexer_clear = body.index_of("\n    lexer_release_parse_source_globals()")
val ast_clear = body.index_of("\n    ast_reset()")
val scope_end = body.index_of("\n    val ended = rt_transient_array_scope_end()")
expect(lexer_clear).to_be_greater_than(scope_end)
expect(ast_clear).to_be_greater_than(lexer_clear)
val assembly = file_read(MODULE_ASSEMBLY)
val assembly_start = assembly.index_of("pub fn parse_and_build_module_scoped")
val assembly_end = assembly.index_of("fn parse_and_build_module(source:")
val assembly_body = assembly.substring(assembly_start, assembly_end)
val assembly_scope_end = assembly_body.index_of("\n        val _ended = rt_transient_array_scope_end()")
val assembly_lexer_clear = assembly_body.index_of("\n        lexer_release_parse_source_globals()")
val assembly_ast_clear = assembly_body.index_of("\n        ast_reset()")
expect(assembly_lexer_clear).to_be_greater_than(assembly_scope_end)
expect(assembly_ast_clear).to_be_greater_than(assembly_lexer_clear)
```

</details>

#### replaces file-local parser owners before reading the next source

- replaces file-local parser owners before reading the next source
   - Expected: init_body does not contain `par_errors.clear()`
   - Expected: init_body does not contain `par_warnings.clear()`
   - Expected: init_body does not contain `par_struct_names.clear()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces file-local parser owners before reading the next source")
val parser = file_read(PARSER)
val init_start = parser.index_of("fn parser_init_with_path")
val init_end = parser.index_of("# Per-token timing probe")
val init_body = parser.substring(init_start, init_end)
expect(init_body).to_contain("par_errors = []")
expect(init_body).to_contain("par_warnings = []")
expect(init_body).to_contain("par_struct_names = []")
expect(init_body.contains("par_errors.clear()")).to_equal(false)
expect(init_body.contains("par_warnings.clear()")).to_equal(false)
expect(init_body.contains("par_struct_names.clear()")).to_equal(false)
expect(init_body).to_contain("parser_generic_constraints_reset()")
val declarations = file_read(FN_STRUCT_DECLS)
expect(declarations).to_contain("fn parser_generic_constraints_reset():")
expect(declarations).to_contain("file_generic_constraints = {}")
expect(declarations).to_contain("file_generic_constraint_modes = {}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage4 streaming surface ownership.
- Stage4 streaming surface ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `417a6a67b6fbf6fe3c25cc9551cd04500946cb89e06b70ec0984b83c58362be2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `417a6a67b6fbf6fe3c25cc9551cd04500946cb89e06b70ec0984b83c58362be2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `417a6a67b6fbf6fe3c25cc9551cd04500946cb89e06b70ec0984b83c58362be2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the complete module surface registry reference-owned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds source 11 and projects it through compact headers and a reference owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains type aliases and required declaration carriers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
