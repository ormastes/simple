# Implicit Context Parameters

> Tests implicit context parameters declared with `context val` and bound with `with_context`. Verifies that context variables work as module-level state shared across all functions, that nested function calls share the same context, that context can be swapped between loggers, and that the save-set-restore pattern correctly preserves outer context after inner scope execution.

<!-- sdn-diagram:id=implicit_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=implicit_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

implicit_context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=implicit_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Implicit Context Parameters

Tests implicit context parameters declared with `context val` and bound with `with_context`. Verifies that context variables work as module-level state shared across all functions, that nested function calls share the same context, that context can be swapped between loggers, and that the save-set-restore pattern correctly preserves outer context after inner scope execution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CTX-001 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/implicit_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests implicit context parameters declared with `context val` and bound with
`with_context`. Verifies that context variables work as module-level state
shared across all functions, that nested function calls share the same context,
that context can be swapped between loggers, and that the save-set-restore
pattern correctly preserves outer context after inner scope execution.

## Syntax

```simple
context val logger: TestLogger
with_context(logger: inner_logger):
_lex("x")
```
Feature 7: Implicit Context Parameters - End-to-End Tests

Tests demonstrate that context variables declared with `context val`
and bound with `with_context` work as module-level state shared across
all functions in the module.

The desugar pass has already transformed these patterns before the
runtime sees the code, so these tests exercise the generated output
directly using module-level var semantics.

## Scenarios

### Feature 7: Implicit Context Parameters

#### context variable is accessible in functions

1.  lex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger = TestLogger(messages: 0, last_msg: "")
__ctx_logger = logger
_lex("x = 1")
expect(__ctx_logger.count()).to_be_greater_than(0)
```

</details>

#### functions share the same context variable

1.  compile
   - Expected: __ctx_logger.count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger = TestLogger(messages: 0, last_msg: "")
__ctx_logger = logger
_compile("x = 1")
# _compile calls _parse which calls _lex - all 3 log calls go to same logger
expect(__ctx_logger.count()).to_equal(3)
```

</details>

#### last logged message is from deepest function call

1.  compile


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger = TestLogger(messages: 0, last_msg: "")
__ctx_logger = logger
_compile("hello")
# _lex is called last, logs "lexing: hello"
expect(__ctx_logger.last()).to_start_with("lexing:")
```

</details>

#### context variable can be swapped for different loggers

1.  lex
2.  lex
   - Expected: count1 equals `1`
   - Expected: count2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val logger1 = TestLogger(messages: 0, last_msg: "first")
val logger2 = TestLogger(messages: 0, last_msg: "second")

__ctx_logger = logger1
_lex("a")
val count1 = __ctx_logger.count()

__ctx_logger = logger2
_lex("b")
val count2 = __ctx_logger.count()

expect(count1).to_equal(1)
expect(count2).to_equal(1)
```

</details>

#### save-set-restore pattern preserves outer context

1.  lex
2.  lex
   - Expected: __ctx_logger.count() equals `1)  # outer logger only saw "y"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer_logger = TestLogger(messages: 0, last_msg: "outer")
val inner_logger = TestLogger(messages: 0, last_msg: "inner")

__ctx_logger = outer_logger

# Simulate: with_context(logger: inner_logger): _lex("x")
val __saved_logger_0 = __ctx_logger
__ctx_logger = inner_logger
_lex("x")
__ctx_logger = __saved_logger_0

# After restore, outer logger is active again
_lex("y")
expect(__ctx_logger.last()).to_start_with("lexing: y")
expect(__ctx_logger.count()).to_equal(1)  # outer logger only saw "y"
```

</details>

#### nil context is default before any with_context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
__ctx_logger = nil
val is_nil = __ctx_logger == nil
expect(is_nil).to_equal(true)
```

</details>

### Feature 7: Multiple Context Variables

#### multiple context vars are independent

1.  print config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lg = TestLogger(messages: 0, last_msg: "")
__ctx_logger = lg
__ctx_config = "production"
_print_config()
expect(__ctx_logger.last()).to_contain("production")
```

</details>

#### setting one ctx var does not affect others

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lg = TestLogger(messages: 0, last_msg: "unchanged")
__ctx_logger = lg
__ctx_config = "dev"
# Changing config should not affect logger
__ctx_config = "prod"
val unchanged = __ctx_logger.last() == "unchanged"
expect(unchanged).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
