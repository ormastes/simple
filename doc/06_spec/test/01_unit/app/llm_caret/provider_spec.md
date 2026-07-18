# Provider Specification

> <details>

<!-- sdn-diagram:id=provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

provider_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Specification

## Scenarios

### Provider List

#### lists all providers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
expect(providers.len()).to_equal(6)
```

</details>

#### includes claude_cli

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "claude_cli":
        found = true
expect(found).to_equal(true)
```

</details>

#### includes opencode_cli

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "opencode_cli":
        found = true
expect(found).to_equal(true)
```

</details>

#### includes claude_api

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "claude_api":
        found = true
expect(found).to_equal(true)
```

</details>

#### includes openai

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "openai":
        found = true
expect(found).to_equal(true)
```

</details>

#### includes openai_compat

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "openai_compat":
        found = true
expect(found).to_equal(true)
```

</details>

#### includes local_torch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers = list_providers()
var found = false
for p in providers:
    if p == "local_torch":
        found = true
expect(found).to_equal(true)
```

</details>

### Provider Validation

#### validates claude_cli

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("claude_cli")).to_equal(true)
```

</details>

#### validates opencode_cli

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("opencode_cli")).to_equal(true)
```

</details>

#### validates claude_api

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("claude_api")).to_equal(true)
```

</details>

#### validates openai

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("openai")).to_equal(true)
```

</details>

#### validates openai_compat

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("openai_compat")).to_equal(true)
```

</details>

#### validates local_torch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("local_torch")).to_equal(true)
```

</details>

#### rejects unknown provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("unknown")).to_equal(false)
```

</details>

#### rejects empty provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_provider("")).to_equal(false)
```

</details>

### LLMResponse Error

#### creates error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = new_llm_error("claude_cli", "connection refused")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("connection refused")
expect(resp.provider).to_equal("claude_cli")
expect(resp.stop_reason).to_equal("error")
expect(resp.content).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Provider List
- Provider Validation
- LLMResponse Error

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
