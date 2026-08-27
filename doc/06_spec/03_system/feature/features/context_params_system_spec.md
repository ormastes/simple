# Context Params System Specification

> <details>

<!-- sdn-diagram:id=context_params_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_params_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_params_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_params_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Params System Specification

## Scenarios

### Context Params: Phase 1 - Module-level context variables

#### context variable starts as nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
__ctx_env = nil
val is_nil = __ctx_env == nil
expect(is_nil).to_equal(true)
```

</details>

#### module var can hold context value (within it block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var local_ctx = nil
local_ctx = "file_logger"
expect(local_ctx).to_equal("file_logger")
```

</details>

#### context variable can be set and restored (within it block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var __ctx_config = "default"
val saved = __ctx_config
__ctx_config = "override"
expect(__ctx_config).to_equal("override")
__ctx_config = saved
expect(__ctx_config).to_equal("default")
```

</details>

#### module-level var is set by module function

1.  set env to test
   - Expected: _get_env() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module function sets module-level var; read back via getter to avoid local shadow
_set_env_to_test()
expect(_get_env()).to_equal("test")
```

</details>

### Context Params: Phase 2 - Desugar output patterns

#### with_context sets and restores context (simulated, within it block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var __ctx_scope: text = "prod"
val saved_scope_0 = __ctx_scope
__ctx_scope = "test"
val result = __ctx_scope + "_mode"
__ctx_scope = saved_scope_0
expect(result).to_equal("test_mode")
expect(__ctx_scope).to_equal("prod")
```

</details>

#### nested with_context uses distinct save vars (within it block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var __ctx_nested: text = "outer"
val __saved_nested_0 = __ctx_nested
__ctx_nested = "middle"
val __saved_nested_1 = __ctx_nested
__ctx_nested = "inner"
val inner_val = __ctx_nested
__ctx_nested = __saved_nested_1
val middle_val = __ctx_nested
__ctx_nested = __saved_nested_0
expect(inner_val).to_equal("inner")
expect(middle_val).to_equal("middle")
expect(__ctx_nested).to_equal("outer")
```

</details>

#### multiple context vars declared in same module

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
__ctx_env = "production"
__ctx_mode = "release"
expect(__ctx_env).to_equal("production")
expect(__ctx_mode).to_equal("release")
```

</details>

#### setting one ctx var does not affect others

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
__ctx_env = "env1"
__ctx_mode = "mode1"
__ctx_env = "env2"
expect(__ctx_mode).to_equal("mode1")
```

</details>

### Context Params: Phase 3 - Full pipeline with context

#### context variable can be used across multiple assignments in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var __ctx_local: text = nil
__ctx_local = "first"
val v1 = __ctx_local
__ctx_local = "second"
val v2 = __ctx_local
__ctx_local = "third"
val v3 = __ctx_local
expect(v1).to_equal("first")
expect(v2).to_equal("second")
expect(v3).to_equal("third")
```

</details>

#### module function modifies context variable and it is visible

1.  set env to test
   - Expected: current equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use getter to read module var (avoids local-shadow issue in it blocks)
_set_env_to_test()
val current = _get_env()
expect(current).to_equal("test")
```

</details>

#### module functions reading module context var (tests core feature)

1.  set env
   - Expected: result equals `test_context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Set via module-level setter so the function sees the same var
_set_env("test_context")
val result = _get_env()
expect(result).to_equal("test_context")
```

</details>

#### module function using context var in computation (tests full feature)

1.  set env
   - Expected: result equals `staging:deploy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Set via module-level setter; _env_aware_op reads the same module var
_set_env("staging")
val result = _env_aware_op("deploy")
expect(result).to_equal("staging:deploy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/context_params_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Context Params: Phase 1 - Module-level context variables
- Context Params: Phase 2 - Desugar output patterns
- Context Params: Phase 3 - Full pipeline with context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
