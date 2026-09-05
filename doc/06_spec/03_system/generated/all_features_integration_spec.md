# All Features Integration Specification

> <details>

<!-- sdn-diagram:id=all_features_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=all_features_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

all_features_integration_spec -> compiler
all_features_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=all_features_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# All Features Integration Specification

## Scenarios

### Integration Feature 1: BackendPort typed fn-field interface

#### BackendPort struct shape

#### has name field identifying the backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
expect(backend.name).to_equal("noop-backend")
```

</details>

#### has supports_jit_fn field callable as fn-field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.supports_jit_fn
val result = f()
expect(result).to_equal(false)
```

</details>

#### has target_triple_fn field callable as fn-field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val backend = services.backend
val f = backend.target_triple_fn
val result = f()
expect(result).to_equal("noop")
```

</details>

#### fn-fields are extracted before calling (chained method workaround)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Runtime limitation: chained calls break, must use intermediate var
val services = create_default_services()
val backend = services.backend
val name = backend.name
expect(name).to_start_with("noop")
```

</details>

### Integration Feature 2: CompilerServices pipeline container

#### all 9 ports accessible via create_default_services

#### creates services container without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
expect(services.lexer.name).to_equal("noop-lexer")
```

</details>

#### has all 9 pipeline stage ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lexer_name = services.lexer.name
val parser_name = services.parser.name
val desugar_name = services.desugarer.name
val checker_name = services.type_checker.name
val hir_name = services.hir_lowerer.name
val mir_name = services.mir_lowerer.name
val backend_name = services.backend.name
val logger_name = services.logger.name
val loader_name = services.module_loader.name
expect(lexer_name).to_equal("noop-lexer")
expect(parser_name).to_equal("noop-parser")
expect(desugar_name).to_equal("noop-desugarer")
expect(checker_name).to_equal("noop-type-checker")
expect(hir_name).to_equal("noop-hir-lowerer")
expect(mir_name).to_equal("noop-mir-lowerer")
expect(backend_name).to_equal("noop-backend")
expect(logger_name).to_equal("noop-logger")
expect(loader_name).to_equal("noop-module-loader")
```

</details>

#### port fn-fields execute noop pipeline steps

#### lexer tokenize_fn returns empty list for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val lexer = services.lexer
val f = lexer.tokenize_fn
val tokens = f("val x = 1")
expect(tokens.len()).to_equal(0)
```

</details>

#### desugarer desugar_fn returns source unchanged for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val desugarer = services.desugarer
val src = "val x = 1"
val f = desugarer.desugar_fn
val result = f(src)
expect(result).to_equal(src)
```

</details>

#### type checker check_fn returns empty errors for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val checker = services.type_checker
val f = checker.check_fn
val errors = f("main.spl")
expect(errors.len()).to_equal(0)
```

</details>

#### module loader resolve_fn returns import name unchanged for noop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val services = create_default_services()
val loader = services.module_loader
val f = loader.resolve_fn
val resolved = f("/src/main.spl", "std.string")
expect(resolved).to_equal("std.string")
```

</details>

### Integration Feature 3: Default Field Values (in progress)

#### placeholder - feature not yet fully implemented in runtime

#### struct construction works with explicitly provided values

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Default field values (field: Type = default) are in progress.
# For now, all fields must be provided explicitly.
# This test verifies the current expected behavior.
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: []
)
expect(rule.module_path).to_equal("src")
```

</details>

#### typed port structs are used with explicit field initialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Once default field values land, ports could use:
#   name: text = "noop"  instead of requiring explicit name
# For now, noop factory functions handle defaults.
val services = create_default_services()
val name = services.lexer.name
expect(name).to_equal("noop-lexer")
```

</details>

### Integration Feature 4: trait keyword desugaring

#### trait converts to struct with fn-fields

#### basic trait header desugars to struct header

1. src = src + "    fn run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var src = "trait Backend:" + NL
src = src + "    fn run(module: text) -> bool" + NL
val out = desugar_traits(src)
expect(out).to_contain("struct Backend:")
```

</details>

#### fn method desugars to fn-field type

1. src = src + "    fn run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var src = "trait Backend:" + NL
src = src + "    fn run(module: text) -> bool" + NL
val out = desugar_traits(src)
expect(out).to_contain("run_fn: fn(text) -> bool")
```

</details>

#### me method desugars to fn-field (mutability stripped)

1. src = src + "    me tokenize


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var src = "trait Lexer:" + NL
src = src + "    me tokenize(src: text) -> [text]" + NL
val out = desugar_traits(src)
expect(out).to_contain("tokenize_fn: fn(text) -> [text]")
```

</details>

#### trait with multiple methods desugars all to fn-fields

1. src = src + "    fn process
2. src = src + "    fn reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var src = "trait PipelineStage:" + NL
src = src + "    fn process(input: text) -> text" + NL
src = src + "    fn reset()" + NL
val out = desugar_traits(src)
expect(out).to_contain("process_fn: fn(text) -> text")
expect(out).to_contain("reset_fn: fn()")
```

</details>

#### impl-for generates factory functions

#### impl-for generates a factory function name

1. src = src + "    fn log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var src = "impl Logger for console:" + NL
src = src + "    fn log(msg: text): print(msg)" + NL
val out = desugar_traits(src)
expect(out).to_contain("fn console_as_Logger")
```

</details>

#### generated factory returns the trait type

1. src = src + "    fn log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var src = "impl Logger for console:" + NL
src = src + "    fn log(msg: text): print(msg)" + NL
val out = desugar_traits(src)
expect(out).to_contain("-> Logger:")
```

</details>

#### non-trait source passes through unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "val x = 1"
val out = desugar_traits(src)
expect(out).to_equal("val x = 1")
```

</details>

### Integration Feature 5: DI Extensions as plugin point

#### DiContainer as dynamic service registry

#### can register and resolve a plugin service

1. di bind instance
   - Expected: plugin equals `my_plugin_impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("plugin_name", "my_plugin_impl")
val plugin = di.resolve("plugin_name")
expect(plugin).to_equal("my_plugin_impl")
```

</details>

#### can register multiple services

1. di bind instance
2. di bind instance
   - Expected: di.has_binding("lexer_plugin") is true
   - Expected: di.has_binding("parser_plugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("lexer_plugin", "custom-lexer")
di.bind_instance("parser_plugin", "custom-parser")
expect(di.has_binding("lexer_plugin")).to_equal(true)
expect(di.has_binding("parser_plugin")).to_equal(true)
```

</details>

#### resolve_or returns default when service not registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
val result = di.resolve_or("missing_plugin", "default_impl")
expect(result).to_equal("default_impl")
```

</details>

#### has returns false for unregistered service

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
expect(di.has_binding("not_registered")).to_equal(false)
```

</details>

#### extensions support factory-based bindings

#### bind registers a factory callable

1. di bind
   - Expected: di.has_binding("backend_factory") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind("backend_factory", fn(): "factory_result")
expect(di.has_binding("backend_factory")).to_equal(true)
```

</details>

#### resolve calls the factory and returns result

1. di bind
   - Expected: version equals `v1.0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind("version", fn(): "v1.0.0")
val version = di.resolve("version")
expect(version).to_equal("v1.0.0")
```

</details>

### Integration Feature 6: Structural Subtyping (in progress)

#### placeholder - feature not yet fully implemented

#### structs with same field names are compatible (placeholder)

1. di bind instance
   - Expected: di.has_binding("arch_rule") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Structural subtyping allows a struct with compatible fields
# to be accepted where another struct type is expected.
# Currently any struct is accepted for Any-typed fields in DI.
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: []
)
# Store and retrieve a typed struct via DI (Any-typed)
di.bind_instance("arch_rule", rule)
expect(di.has_binding("arch_rule")).to_equal(true)
```

</details>

#### typed port structs demonstrate composition over inheritance

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BackendPort and LexerPort are separate structs with fn-fields.
# Both share the 'name' field - structural compatibility principle.
val services = create_default_services()
val backend_name = services.backend.name
val lexer_name = services.lexer.name
expect(backend_name.len() > 0).to_equal(true)
expect(lexer_name.len() > 0).to_equal(true)
```

</details>

### Integration Feature 7: Implicit Context Parameters (in progress)

#### placeholder - context val / with_context not yet implemented

#### explicit context passing works as current workaround

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Until implicit context params land, services are passed explicitly.
# This demonstrates the intended usage pattern:
#   context val services: CompilerServices  -- future syntax
#   services.lexer.tokenize_fn("input")     -- implicit use
# Current workaround: pass services as explicit parameter.
val services = create_default_services()
val f = services.lexer.tokenize_fn
val result = f("val x = 1")
expect(result.len()).to_equal(0)
```

</details>

#### DI container provides context-like dependency resolution

1. di bind instance
   - Expected: version equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DiContainer serves as explicit context registry until
# implicit context parameters are implemented.
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("context_version", "1.0")
val version = di.resolve("context_version")
expect(version).to_equal("1.0")
```

</details>

### Integration Feature 8: Architecture validation

#### arch rule pattern matching

#### matches exact module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matched = _match_pattern("core/ast", "core/ast")
expect(matched).to_equal(true)
```

</details>

#### glob /** matches sub-paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matched = _match_pattern("compiler/backend/jit", "compiler/**")
expect(matched).to_equal(true)
```

</details>

#### denies import matching deny pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: ["compiler/**"]
)
val allowed = _is_import_allowed("compiler/backend", rule)
expect(allowed).to_equal(false)
```

</details>

#### allows import not matching deny pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: ["compiler/**"]
)
val allowed = _is_import_allowed("core/ast", rule)
expect(allowed).to_equal(true)
```

</details>

#### allows import matching allow pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**", "std/**"],
    deny_patterns: []
)
val allowed = _is_import_allowed("core/ast", rule)
expect(allowed).to_equal(true)
```

</details>

#### arch check runs on project

#### project source directory is accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("test -d src && echo yes")
val trimmed = result.stdout.trim()
expect(trimmed).to_equal("yes")
```

</details>

#### arch_check source file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("test -f src/app/cli/arch_check.spl && echo yes")
val trimmed = result.stdout.trim()
expect(trimmed).to_equal("yes")
```

</details>

#### check-arch command is wired into main CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("grep -c 'check-arch' src/app/cli/main.spl")
val count = int(result.stdout.trim())
expect(count > 0).to_equal(true)
```

</details>

### Integration Feature 9: DI Lock

#### explicit lock prevents modifications

#### is_locked returns false before locking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
expect(di.is_locked()).to_equal(false)
```

</details>

#### is_locked returns true after lock()

1. di lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### locked container rejects bind_instance

1. di lock
2. di bind instance
   - Expected: di.has_binding("new_key") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_instance("new_key", "new_val")
expect(di.has_binding("new_key")).to_equal(false)
```

</details>

#### locked container rejects bind factory

1. di lock
2. di bind
   - Expected: di.has_binding("blocked_key") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind("blocked_key", fn(): "blocked")
expect(di.has_binding("blocked_key")).to_equal(false)
```

</details>

#### resolve still works when locked

1. di bind instance
2. di lock
   - Expected: result equals `production-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("pre_lock_svc", "production-value")
di.lock()
val result = di.resolve("pre_lock_svc")
expect(result).to_equal("production-value")
```

</details>

#### unlock allows new bindings after lock

1. di lock
2. di bind instance
   - Expected: di.has_binding("blocked") is false
3. di unlock
4. di bind instance
   - Expected: di.has_binding("allowed") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_instance("blocked", "x")
expect(di.has_binding("blocked")).to_equal(false)
di.unlock()
di.bind_instance("allowed", "y")
expect(di.has_binding("allowed")).to_equal(true)
```

</details>

#### env-var lock (system test protection)

#### SIMPLE_SYSTEM_TEST=1 blocks bind operations

1. rt env set
2. rt env set
3. di bind instance
   - Expected: di.has_binding("mock_svc") is false
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("mock_svc", "mock")
expect(di.has_binding("mock_svc")).to_equal(false)
# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### SIMPLE_DI_TEST=1 bypasses env-var lock

1. rt env set
2. rt env set
3. di bind instance
   - Expected: di.has_binding("test_svc") is true
4. rt env set
5. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("test_svc", "test_val")
expect(di.has_binding("test_svc")).to_equal(true)
# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

### Integration: Full mini-compiler pipeline (all 9 features)

#### simulated compile-a-file scenario

#### Step 1+2: create typed service container (Features 1+2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feature 2: CompilerServices groups all 9 pipeline ports
# Feature 1: BackendPort is one of those typed ports
val services = create_default_services()
expect(services.backend.name).to_equal("noop-backend")
expect(services.lexer.name).to_equal("noop-lexer")
```

</details>

#### Step 4: desugar trait to struct before parse (Feature 4)

1. source = source + "    fn transform


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feature 4: trait keyword desugars to struct with fn-fields
var source = "trait Transformer:" + NL
source = source + "    fn transform(input: text) -> text" + NL
val desugared = desugar_traits(source)
expect(desugared).to_contain("struct Transformer:")
expect(desugared).to_contain("transform_fn: fn(text) -> text")
```

</details>

#### Step 4+2: desugared struct matches port pattern (Features 4+2)

1. source = source + "    fn tokenize


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A trait-desugared struct has the same shape as compiler port structs:
# both are structs with fn-fields. This is the core design pattern.
var source = "trait LexerPlugin:" + NL
source = source + "    fn tokenize(src: text) -> [text]" + NL
val desugared = desugar_traits(source)
# Same fn-field pattern as LexerPort.tokenize_fn
expect(desugared).to_contain("tokenize_fn: fn(text) -> [text]")
```

</details>

#### Step 5: register plugin via DI extensions (Feature 5)

1. di bind instance
2. di bind instance
   - Expected: di.has_binding("custom_lexer") is true
   - Expected: di.has_binding("custom_formatter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feature 5: extensions DiContainer is the plugin point
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("custom_lexer", "regex-lexer-plugin")
di.bind_instance("custom_formatter", "pretty-printer-plugin")
expect(di.has_binding("custom_lexer")).to_equal(true)
expect(di.has_binding("custom_formatter")).to_equal(true)
```

</details>

#### Step 5+2: run noop pipeline stages from CompilerServices (Features 5+2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate running source through the pipeline stages
val services = create_default_services()
val source = "val x = 42"

# Stage 1: Tokenize
val lex_fn = services.lexer.tokenize_fn
val tokens = lex_fn(source)

# Stage 2: Parse
val parse_fn = services.parser.parse_fn
val ast_errors = parse_fn(tokens, source)

# Stage 3: Type check
val check_fn = services.type_checker.check_fn
val type_errors = check_fn("main")

expect(tokens.len()).to_equal(0)
expect(ast_errors.len()).to_equal(0)
expect(type_errors.len()).to_equal(0)
```

</details>

#### Step 9: lock DI after setup (Feature 9)

1. di bind instance
2. di bind instance
3. di lock
   - Expected: di.resolve("backend") equals `interpreter-backend`
   - Expected: di.resolve("logger") equals `file-logger`
4. di bind instance
   - Expected: di.has_binding("attack_service") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feature 9: lock the container after wiring up all services
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("backend", "interpreter-backend")
di.bind_instance("logger", "file-logger")
di.lock()

# Services are accessible
expect(di.resolve("backend")).to_equal("interpreter-backend")
expect(di.resolve("logger")).to_equal("file-logger")

# But no new services can be injected after lock
di.bind_instance("attack_service", "malicious-mock")
expect(di.has_binding("attack_service")).to_equal(false)
```

</details>

#### Step 8: verify architecture rules via check_arch (Feature 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feature 8: arch check validates module dependency rules
val rule_no_deny = ArchRule(
    init_file: "test/__init__.spl",
    module_path: "test",
    allow_patterns: [],
    deny_patterns: []
)
# With no deny rules, any import is allowed
val ok = _is_import_allowed("compiler/backend", rule_no_deny)
expect(ok).to_equal(true)
```

</details>

#### Pipeline: all port names follow naming convention (Features 1+2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All noop port names start with "noop-" by convention
val services = create_default_services()
expect(services.lexer.name).to_start_with("noop")
expect(services.parser.name).to_start_with("noop")
expect(services.desugarer.name).to_start_with("noop")
expect(services.type_checker.name).to_start_with("noop")
expect(services.hir_lowerer.name).to_start_with("noop")
expect(services.mir_lowerer.name).to_start_with("noop")
expect(services.backend.name).to_start_with("noop")
expect(services.logger.name).to_start_with("noop")
expect(services.module_loader.name).to_start_with("noop")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/all_features_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Integration Feature 1: BackendPort typed fn-field interface
- Integration Feature 2: CompilerServices pipeline container
- Integration Feature 3: Default Field Values (in progress)
- Integration Feature 4: trait keyword desugaring
- Integration Feature 5: DI Extensions as plugin point
- Integration Feature 6: Structural Subtyping (in progress)
- Integration Feature 7: Implicit Context Parameters (in progress)
- Integration Feature 8: Architecture validation
- Integration Feature 9: DI Lock
- Integration: Full mini-compiler pipeline (all 9 features)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
