# Js Native Confinement Specification

> Tests covering JS native confinement (node capability gating).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Native Confinement Specification

## Scenarios

### JS native confinement (node capability gating)

#### denies require('process') to untrusted page script

- page script asks for the process module
- no callable exit surfaces from the module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("page script asks for the process module")
val verdict = probe(untrusted_runtime(), "typeof require('process').exit")
step("no callable exit surfaces from the module")
expect(verdict).to_not_equal("function")
```

</details>

#### denies require('os') to untrusted page script

- page script asks for the os module
- no callable platform probe surfaces from the module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("page script asks for the os module")
val verdict = probe(untrusted_runtime(), "typeof require('os').platform")
step("no callable platform probe surfaces from the module")
expect(verdict).to_not_equal("function")
```

</details>

#### keeps process.exit uninvocable from untrusted page script

- page script tries to terminate the host, then reports back
- a direct exit call errors instead of terminating the host
   - Expected: survived equals `<err>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("page script tries to terminate the host, then reports back")
val exit_type = probe(untrusted_runtime(), "typeof process.exit")
expect(exit_type).to_not_equal("function")
step("a direct exit call errors instead of terminating the host")
val survived = probe(untrusted_runtime(), "process.exit(3)")
expect(survived).to_equal("<err>")
```

</details>

#### hides the host cwd from untrusted page script

- page script tries to read the working directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("page script tries to read the working directory")
val cwd_type = probe(untrusted_runtime(), "typeof process.cwd")
expect(cwd_type).to_not_equal("function")
```

</details>

#### still serves require('os') to a trusted embedder

- trusted embedder (node compat granted) asks for os
   - Expected: verdict equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("trusted embedder (node compat granted) asks for os")
val verdict = probe(trusted_runtime(), "typeof require('os').platform")
expect(verdict).to_equal("function")
```

</details>

#### still serves require('process') to a trusted embedder

- trusted embedder asks for process
   - Expected: verdict equals `object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("trusted embedder asks for process")
val verdict = probe(trusted_runtime(), "typeof require('process')")
expect(verdict).to_equal("object")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/js_native_confinement_spec.spl` |
| Updated | 2026-08-15 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS native confinement (node capability gating).
- JS native confinement (node capability gating)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
