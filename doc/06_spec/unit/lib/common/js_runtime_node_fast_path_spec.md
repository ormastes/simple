# Js Runtime Node Fast Path Specification

## Scenarios

### JsRuntime Node host fast paths

#### fast paths process cwd probes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_runtime_eval_text("process.cwd()")).to_equal("/")
expect(_runtime_eval_text("require('process').cwd()")).to_equal("/")
expect(_runtime_eval_text("require(\"process\").cwd()")).to_equal("/")
```

</details>

#### fast paths process argv probes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_runtime_eval_text("process.argv.length")).to_equal("2")
expect(_runtime_eval_text("process.argv[0]")).to_equal("simple")
expect(_runtime_eval_text("require('process').argv.length")).to_equal("2")
```

</details>

#### fast paths Buffer byteLength probes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_runtime_eval_text("require('buffer').Buffer.byteLength('hello', 'utf8')")).to_equal("5")
expect(_runtime_eval_text("require(\"buffer\").Buffer.byteLength(\"hello\", \"utf8\")")).to_equal("5")
```

</details>

#### fast paths Buffer.from toString probes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_runtime_eval_text("require('buffer').Buffer.from('68656c6c6f', 'hex').toString('utf8')")).to_equal("hello")
expect(_runtime_eval_text("require(\"buffer\").Buffer.from(\"68656c6c6f\", \"hex\").toString(\"utf8\")")).to_equal("hello")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/js_runtime_node_fast_path_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JsRuntime Node host fast paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

