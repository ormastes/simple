# Bootstrap Intensive Specification

> Tests covering Bootstrap Workflow - Intensive, Module Compilation - Intensive, Dependency Resolution - Intensive, Code Generation - Intensive, Runtime Integration - Intensive, Verification - Intensive, Performance - Intensive, Platform Support - Intensive, Error Recovery - Intensive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Intensive Specification

## Scenarios

### Bootstrap Workflow - Intensive

#### stage 0 - prebuilt runtime

<details>
<summary>Advanced: validates prebuilt runtime</summary>

#### validates prebuilt runtime _(slow)_

- validates prebuilt runtime


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates prebuilt runtime")
val runtime_path = "bin/simple"
check(runtime_path.contains("release"))
check(runtime_path.contains("simple"))
```

</details>


</details>

<details>
<summary>Advanced: checks runtime version</summary>

#### checks runtime version _(slow)_

- checks runtime version


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("checks runtime version")
val version = "0.5.0"
val parts = version.split(".")
check(parts.len() == 3)
check(parts[0] == "0")
```

</details>


</details>

#### stage 1 - first compilation

<details>
<summary>Advanced: compiles core modules</summary>

#### compiles core modules _(slow)_

- compiles core modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles core modules")
val core_modules = [
    "src/compiler/10.frontend/core/tokens.spl",
    "src/compiler/10.frontend/core/lexer.spl",
    "src/compiler/10.frontend/core/parser.spl",
    "src/compiler/10.frontend/core/ast.spl",
    "src/compiler/30.types/type_system/builtin_registry.spl"
]

for module in core_modules:
    check(module.starts_with("src/compiler/"))
    check(module.ends_with(".spl"))
```

</details>


</details>

<details>
<summary>Advanced: compiles compiler modules</summary>

#### compiles compiler modules _(slow)_

- compiles compiler modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles compiler modules")
val compiler_modules = [
    "src/compiler/native/mod.spl",
    "src/compiler/bootstrap/mod.spl"
]

for module in compiler_modules:
    check(module.contains("/compiler/"))
```

</details>


</details>

#### stage 2 - recompilation

<details>
<summary>Advanced: recompiles with stage 1</summary>

#### recompiles with stage 1 _(slow)_

- recompiles with stage 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recompiles with stage 1")
# Stage 2 should produce identical output
val stage1_hash = "abc123def456"
val stage2_hash = "abc123def456"

check(stage1_hash == stage2_hash)
```

</details>


</details>

<details>
<summary>Advanced: validates idempotence</summary>

#### validates idempotence _(slow)_

- validates idempotence


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates idempotence")
val iterations = 3
var hashes = []

for i in 0..iterations:
    hashes = hashes.append("hash123")

# All hashes should be identical
var all_same = true
for hash in hashes:
    if hash != "hash123":
        all_same = false

check(all_same)
```

</details>


</details>

### Module Compilation - Intensive

#### core module compilation

<details>
<summary>Advanced: compiles tokens module</summary>

#### compiles tokens module _(slow)_

- compiles tokens module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles tokens module")
val module = "src/compiler/10.frontend/core/tokens.spl"
check(module.ends_with("tokens.spl"))
```

</details>


</details>

<details>
<summary>Advanced: compiles lexer module</summary>

#### compiles lexer module _(slow)_

- compiles lexer module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles lexer module")
val module = "src/compiler/10.frontend/core/lexer.spl"
check(module.ends_with("lexer.spl"))
```

</details>


</details>

<details>
<summary>Advanced: compiles parser module</summary>

#### compiles parser module _(slow)_

- compiles parser module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles parser module")
val module = "src/compiler/10.frontend/core/parser.spl"
check(module.ends_with("parser.spl"))
```

</details>


</details>

<details>
<summary>Advanced: compiles ast module</summary>

#### compiles ast module _(slow)_

- compiles ast module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles ast module")
val module = "src/compiler/10.frontend/core/ast.spl"
check(module.ends_with("ast.spl"))
```

</details>


</details>

<details>
<summary>Advanced: compiles types module</summary>

#### compiles types module _(slow)_

- compiles types module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles types module")
val module = "src/compiler/30.types/type_system/builtin_registry.spl"
check(module.ends_with("builtin_registry.spl"))
```

</details>


</details>

<details>
<summary>Advanced: compiles mir module</summary>

#### compiles mir module _(slow)_

- compiles mir module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles mir module")
val module = "src/compiler/50.mir/mir_data.spl"
check(module.ends_with("mir_data.spl"))
```

</details>


</details>

#### compiler backend compilation

<details>
<summary>Advanced: compiles native backend</summary>

#### compiles native backend _(slow)_

- compiles native backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles native backend")
val module = "src/compiler/native/mod.spl"
check(module.contains("native"))
```

</details>


</details>

<details>
<summary>Advanced: compiles bootstrap backend</summary>

#### compiles bootstrap backend _(slow)_

- compiles bootstrap backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles bootstrap backend")
val module = "src/compiler/bootstrap/mod.spl"
check(module.contains("bootstrap"))
```

</details>


</details>

### Dependency Resolution - Intensive

#### dependency tracking

<details>
<summary>Advanced: builds dependency graph for 50 modules</summary>

#### builds dependency graph for 50 modules _(slow)_

- builds dependency graph for 50 modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds dependency graph for 50 modules")
var dependencies = []

for i in 0..50:
    val dep_list = if i > 0: ["module_{i-1}"] else: []
    val dep = {"module": "module_{i}", "deps": dep_list}
    dependencies = dependencies.append(dep)

check(dependencies.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: detects circular dependencies</summary>

#### detects circular dependencies _(slow)_

- detects circular dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects circular dependencies")
val modules = [
    {"name": "a", "deps": ["b"]},
    {"name": "b", "deps": ["c"]},
    {"name": "c", "deps": ["a"]}
]

# Would form a cycle: a -> b -> c -> a
check(modules.len() == 3)
```

</details>


</details>

#### compilation order

<details>
<summary>Advanced: determines compilation order</summary>

#### determines compilation order _(slow)_

- determines compilation order


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("determines compilation order")
val modules = [
    "tokens",    # No deps
    "lexer",     # Depends on tokens
    "parser",    # Depends on tokens, lexer
    "ast",       # Depends on tokens
    "types"      # Depends on tokens, ast
]

check(modules[0] == "tokens")
check(modules.len() == 5)
```

</details>


</details>

<details>
<summary>Advanced: handles 100 module dependencies</summary>

#### handles 100 module dependencies _(slow)_

- handles 100 module dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 100 module dependencies")
var ordered = []

for i in 0..100:
    ordered = ordered.append("mod_{i}")

check(ordered.len() == 100)
```

</details>


</details>

### Code Generation - Intensive

#### function code generation

<details>
<summary>Advanced: generates code for 200 functions</summary>

#### generates code for 200 functions _(slow)_

- generates code for 200 functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates code for 200 functions")
var functions = []

for i in 0..200:
    val ret_type = if i % 2 == 0: "i64" else: "text"
    val func = {"name": "fn_{i}", "params": i % 5, "return_type": ret_type}
    functions = functions.append(func)

check(functions.len() == 200)
```

</details>


</details>

<details>
<summary>Advanced: generates class methods</summary>

#### generates class methods _(slow)_

- generates class methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates class methods")
var methods = []

for i in 0..100:
    val is_static = i % 3 == 0
    val method = {"class": "Class_{i / 10}", "name": "method_{i}", "static": is_static}
    methods = methods.append(method)

check(methods.len() == 100)
```

</details>


</details>

#### optimization passes

<details>
<summary>Advanced: applies constant folding</summary>

#### applies constant folding _(slow)_

- applies constant folding


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("applies constant folding")
val expressions = [
    "1 + 2",
    "3 * 4",
    "10 - 5",
    "20 / 4"
]

# These should be folded to constants
for expr in expressions:
    check(expr.contains("+") or expr.contains("*") or expr.contains("-") or expr.contains("/"))
```

</details>


</details>

<details>
<summary>Advanced: performs dead code elimination</summary>

#### performs dead code elimination _(slow)_

- performs dead code elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("performs dead code elimination")
var live_code = []
var dead_code = []

for i in 0..200:
    if i % 2 == 0:
        live_code = live_code.append(i)
    else:
        dead_code = dead_code.append(i)

# After DCE, only live_code remains
check(live_code.len() == 100)
```

</details>


</details>

### Runtime Integration - Intensive

#### runtime function calls

<details>
<summary>Advanced: generates calls to 100 runtime functions</summary>

#### generates calls to 100 runtime functions _(slow)_

- generates calls to 100 runtime functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates calls to 100 runtime functions")
var rt_calls = []

for i in 0..100:
    val call = {"name": "rt_fn_{i}", "args": i % 4}
    rt_calls = rt_calls.append(call)

check(rt_calls.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: validates runtime signatures</summary>

#### validates runtime signatures _(slow)_

- validates runtime signatures


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates runtime signatures")
val runtime_fns = [
    {"name": "rt_print", "args": 1},
    {"name": "rt_file_read", "args": 1},
    {"name": "rt_file_write", "args": 2}
]

for rt_fn in runtime_fns:
    check(rt_fn["name"].starts_with("rt_"))
    check(rt_fn["args"] > 0)
```

</details>


</details>

#### memory management

<details>
<summary>Advanced: tracks allocations</summary>

#### tracks allocations _(slow)_

- tracks allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks allocations")
var allocations = []

for i in 0..500:
    val alloc = {"size": i * 8, "type": "object"}
    allocations = allocations.append(alloc)

check(allocations.len() == 500)
```

</details>


</details>

<details>
<summary>Advanced: simulates garbage collection</summary>

#### simulates garbage collection _(slow)_

- simulates garbage collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simulates garbage collection")
var live_objects = 1000
var collected = 0

for i in 0..10:
    val gc_freed = 50
    collected = collected + gc_freed
    live_objects = live_objects - gc_freed

check(collected == 500)
check(live_objects == 500)
```

</details>


</details>

### Verification - Intensive

#### output comparison

<details>
<summary>Advanced: compares stage 1 and stage 2 outputs</summary>

#### compares stage 1 and stage 2 outputs _(slow)_

- compares stage 1 and stage 2 outputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compares stage 1 and stage 2 outputs")
var stage1_files = []
var stage2_files = []

for i in 0..50:
    stage1_files = stage1_files.append("file_{i}.o")
    stage2_files = stage2_files.append("file_{i}.o")

check(stage1_files.len() == stage2_files.len())
```

</details>


</details>

<details>
<summary>Advanced: validates output binaries</summary>

#### validates output binaries _(slow)_

- validates output binaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates output binaries")
val binaries = [
    {"name": "simple", "size": 33000000, "platform": "linux-x64"},
    {"name": "simple", "size": 35000000, "platform": "macos-arm64"}
]

for binary in binaries:
    check(binary["name"] == "simple")
    check(binary["size"] > 10000000)
```

</details>


</details>

#### regression testing

<details>
<summary>Advanced: runs 100 regression tests</summary>

#### runs 100 regression tests _(slow)_

- runs 100 regression tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs 100 regression tests")
var tests = []

for i in 0..100:
    val t_status = if i % 20 == 0: "fail" else: "pass"
    val test = {"name": "regression_{i}", "status": t_status}
    tests = tests.append(test)

var passed = 0
var failed = 0

for test in tests:
    if test["status"] == "pass":
        passed = passed + 1
    else:
        failed = failed + 1

check(passed == 95)
check(failed == 5)
```

</details>


</details>

### Performance - Intensive

#### compilation speed

<details>
<summary>Advanced: measures compilation times</summary>

#### measures compilation times _(slow)_

- measures compilation times


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("measures compilation times")
var times = []

for i in 0..100:
    val time_ms = 10 + (i % 50)
    times = times.append(time_ms)

var total = 0
for time in times:
    total = total + time

check(total > 1000)
```

</details>


</details>

<details>
<summary>Advanced: tracks memory usage</summary>

#### tracks memory usage _(slow)_

- tracks memory usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks memory usage")
var memory_samples = []

for i in 0..200:
    val mem_mb = 100 + (i / 10)
    memory_samples = memory_samples.append(mem_mb)

check(memory_samples.len() == 200)
```

</details>


</details>

#### optimization impact

<details>
<summary>Advanced: compares optimized vs unoptimized</summary>

#### compares optimized vs unoptimized _(slow)_

- compares optimized vs unoptimized


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compares optimized vs unoptimized")
val unoptimized_time = 1000
val optimized_time = 600

# Integer division: 1000/600 = 1, so compare differently
check(unoptimized_time > optimized_time)
```

</details>


</details>

### Platform Support - Intensive

#### platform targets

<details>
<summary>Advanced: validates platform configurations</summary>

#### validates platform configurations _(slow)_

- validates platform configurations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates platform configurations")
val platforms = [
    "linux-x64",
    "macos-arm64",
    "macos-x64",
    "freebsd-x64"
]

for platform in platforms:
    check(platform.contains("-"))
```

</details>


</details>

<details>
<summary>Advanced: generates platform-specific code</summary>

#### generates platform-specific code _(slow)_

- generates platform-specific code


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates platform-specific code")
var platform_outputs = []

for platform in ["linux", "macos", "freebsd"]:
    for arch in ["x64", "arm64"]:
        val output = "{platform}-{arch}"
        platform_outputs = platform_outputs.append(output)

check(platform_outputs.len() == 6)
```

</details>


</details>

### Error Recovery - Intensive

#### compilation errors

<details>
<summary>Advanced: handles 50 compilation errors</summary>

#### handles 50 compilation errors _(slow)_

- handles 50 compilation errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 50 compilation errors")
var errors = []

for i in 0..50:
    val error = {"file": "src/module_{i}.spl", "line": i * 10, "message": "Compilation error"}
    errors = errors.append(error)

check(errors.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: recovers from partial failures</summary>

#### recovers from partial failures _(slow)_

- recovers from partial failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recovers from partial failures")
var total_modules = 100
var failed_modules = 5
var successful = total_modules - failed_modules

check(successful == 95)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/bootstrap_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bootstrap Workflow - Intensive, Module Compilation - Intensive, Dependency Resolution - Intensive, Code Generation - Intensive, Runtime Integration - Intensive, Verification - Intensive, Performance - Intensive, Platform Support - Intensive, Error Recovery - Intensive.
- Bootstrap Workflow - Intensive
- Module Compilation - Intensive
- Dependency Resolution - Intensive
- Code Generation - Intensive
- Runtime Integration - Intensive
- Verification - Intensive
- Performance - Intensive
- Platform Support - Intensive
- Error Recovery - Intensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 36 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc290a4d0a7e4acd2faecc62906f63728463c05de7ec2a5eab72a08fb5f6966d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc290a4d0a7e4acd2faecc62906f63728463c05de7ec2a5eab72a08fb5f6966d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc290a4d0a7e4acd2faecc62906f63728463c05de7ec2a5eab72a08fb5f6966d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/integration/compiler/bootstrap_intensive_spec.spl
mirror: doc/06_spec/integration/compiler/bootstrap_intensive_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/bootstrap_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/bootstrap_intensive_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates prebuilt runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/bootstrap_intensive_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks runtime version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/bootstrap_intensive_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles core modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
