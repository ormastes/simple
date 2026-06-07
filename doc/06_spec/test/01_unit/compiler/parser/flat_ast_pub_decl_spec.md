# Flat Ast Pub Decl Specification

> <details>

<!-- sdn-diagram:id=flat_ast_pub_decl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=flat_ast_pub_decl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

flat_ast_pub_decl_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=flat_ast_pub_decl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Ast Pub Decl Specification

## Scenarios

### Flat AST bridge public declaration parsing

#### accepts top-level pub fn on the active frontend path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "pub fn api() -> i64:\n    1\n"
val module = parse_and_build_module(src, "test_pub_fn.spl")

expect(module.functions.contains("api")).to_equal(true)
val api = module.functions["api"] ?? panic("missing api function")
expect(api.visibility).to_equal(Visibility.Public)
expect(api.is_public).to_equal(true)
```

</details>

#### preserves GPU target decorators on the active frontend path

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@gpu(\"opencl\")\nfn opencl_kernel(value: u32) -> u32:\n    value\n"
val module = parse_and_build_module(src, "test_gpu_opencl_fn.spl")

expect(module.functions.contains("opencl_kernel")).to_equal(true)
val kernel = module.functions["opencl_kernel"] ?? panic("missing opencl kernel function")
expect(kernel.is_kernel).to_equal(true)
expect(kernel.attributes.len()).to_equal(1)
expect(kernel.attributes[0].name).to_equal("gpu")
expect(kernel.attributes[0].args.len()).to_equal(1)
match kernel.attributes[0].args[0].kind:
    case StringLit(value, _):
        expect(value).to_equal("opencl")
    case _:
        expect(false).to_equal(true)
```

</details>

#### preserves named GPU target decorator arguments on the active frontend path

<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@gpu(target=\"opencl\")\nfn named_opencl_kernel(value: u32) -> u32:\n    value\n"
val module = parse_and_build_module(src, "test_named_gpu_opencl_fn.spl")

expect(module.functions.contains("named_opencl_kernel")).to_equal(true)
val kernel = module.functions["named_opencl_kernel"] ?? panic("missing named opencl kernel function")
expect(kernel.is_kernel).to_equal(true)
expect(kernel.attributes.len()).to_equal(1)
expect(kernel.attributes[0].name).to_equal("gpu")
expect(kernel.attributes[0].args.len()).to_equal(1)
match kernel.attributes[0].args[0].kind:
    case Assign(left, _, right):
        match left.kind:
            case Ident(name):
                expect(name).to_equal("target")
            case _:
                expect(false).to_equal(true)
        match right.kind:
            case StringLit(value, _):
                expect(value).to_equal("opencl")
            case _:
                expect(false).to_equal(true)
    case _:
        expect(false).to_equal(true)
```

</details>

#### accepts top-level pub const-style binding on the active frontend path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "pub val answer: i64 = 42\n"
val module = parse_and_build_module(src, "test_pub_val.spl")

expect(module.constants.contains("answer")).to_equal(true)
val answer = module.constants["answer"] ?? panic("missing answer constant")
expect(answer.visibility).to_equal(Visibility.Public)
expect(answer.is_public).to_equal(true)
```

</details>

#### preserves scoped peer and up visibility on the active frontend path

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "pub(peer) fn peer_api() -> i64:\n    1\n\npub(up) val parent_api: i64 = 2\n\npri fn hidden_api() -> i64:\n    3\n"
val module = parse_and_build_module(src, "test_scoped_visibility.spl")

expect(module.functions.contains("peer_api")).to_equal(true)
val peer_api = module.functions["peer_api"] ?? panic("missing peer_api function")
expect(peer_api.visibility).to_equal(Visibility.Peer)
expect(peer_api.is_public).to_equal(false)

expect(module.functions.contains("hidden_api")).to_equal(true)
val hidden_api = module.functions["hidden_api"] ?? panic("missing hidden_api function")
expect(hidden_api.visibility).to_equal(Visibility.Private)
expect(hidden_api.is_public).to_equal(false)

expect(module.constants.contains("parent_api")).to_equal(true)
val parent_api = module.constants["parent_api"] ?? panic("missing parent_api constant")
expect(parent_api.visibility).to_equal(Visibility.Up)
expect(parent_api.is_public).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/flat_ast_pub_decl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Flat AST bridge public declaration parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
