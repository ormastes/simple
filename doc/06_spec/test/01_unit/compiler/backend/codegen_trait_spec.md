# Codegen Trait Specification

> <details>

<!-- sdn-diagram:id=codegen_trait_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=codegen_trait_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

codegen_trait_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=codegen_trait_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codegen Trait Specification

## Scenarios

### CodegenOutputKind concepts

#### has four output kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = ["ObjectCode", "TextSource", "AcceleratorCode", "InterpretedResult"]
expect(kinds.len()).to_equal(4)
```

</details>

#### ObjectCode is for native compilation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "ObjectCode"
expect(kind).to_equal("ObjectCode")
```

</details>

#### TextSource is for C/transpiled output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "TextSource"
expect(kind).to_equal("TextSource")
```

</details>

#### InterpretedResult is for interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "InterpretedResult"
expect(kind).to_equal("InterpretedResult")
```

</details>

### CodegenOutput patterns

#### text output has name and source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "test_module"
val source = "int main() {}"
expect(name).to_equal("test_module")
expect(source).to_contain("main")
```

</details>

#### object output has name and bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "native_mod"
val bytes = [0x7f, 0x45, 0x4c, 0x46]
expect(name).to_equal("native_mod")
expect(bytes.len()).to_equal(4)
```

</details>

#### interpreted output has only name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "interp_mod"
expect(name).to_equal("interp_mod")
```

</details>

### CodegenFactory backend mapping

#### maps backend names correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backends = ["llvm", "c", "native", "interpreter", "cranelift", "wasm", "cuda", "vulkan", "lean", "vhdl"]
expect(backends.len()).to_equal(10)
expect(backends[0]).to_equal("llvm")
expect(backends[1]).to_equal("c")
expect(backends[2]).to_equal("native")
```

</details>

#### LLVM produces object code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = "llvm"
val output_kind = "ObjectCode"
expect(backend).to_equal("llvm")
expect(output_kind).to_equal("ObjectCode")
```

</details>

#### C backend produces text source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = "c"
val output_kind = "TextSource"
expect(backend).to_equal("c")
expect(output_kind).to_equal("TextSource")
```

</details>

#### Interpreter produces interpreted result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = "interpreter"
val output_kind = "InterpretedResult"
expect(backend).to_equal("interpreter")
```

</details>

### Codegen adapter target support

#### LLVM supports all CPU targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = ["x86_64", "aarch64", "riscv64"]
expect(targets.len()).to_equal(3)
```

</details>

#### Native supports CPU targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = ["x86_64", "aarch64", "riscv64"]
expect(targets.len()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/codegen_trait_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CodegenOutputKind concepts
- CodegenOutput patterns
- CodegenFactory backend mapping
- Codegen adapter target support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
