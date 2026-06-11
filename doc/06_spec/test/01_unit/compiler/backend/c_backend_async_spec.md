# C Backend Async Specification

> 1. LocalId

<!-- sdn-diagram:id=c_backend_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=c_backend_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

c_backend_async_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=c_backend_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Backend Async Specification

## Scenarios

### C backend async lowering

#### emits explicit panic code for CreatePromise

1. LocalId
2. LocalId
3. MirType promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = output_for(\translator:
    translator.translate_create_promise(
        LocalId(id: 1),
        LocalId(id: 2),
        MirType.promise(MirType.i64())
    )
)

expect(output).to_contain("spl_panic(\"C backend does not support async CreatePromise lowering\")")
```

</details>

#### emits explicit panic code for Await and Yield

1. translator translate await
2. translator translate yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = output_for(\translator:
    translator.translate_await(LocalId(id: 1), MirOperand.const_int(7))
    translator.translate_yield(Some(MirOperand.const_int(9)))
)

expect(output).to_contain("spl_panic(\"C backend does not support async Await lowering\")")
expect(output).to_contain("spl_panic(\"C backend does not support async Yield lowering\")")
```

</details>

#### emits explicit panic code for Spawn, Send, and Receive

1. translator translate spawn
2. translator translate send
3. translator translate receive


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = output_for(\translator:
    translator.translate_spawn(LocalId(id: 1), MirOperand.const_int(0), [MirOperand.const_int(1), MirOperand.const_int(2)])
    translator.translate_send(MirOperand.const_int(3), MirOperand.const_int(4))
    translator.translate_receive(LocalId(id: 2), nil)
)

expect(output).to_contain("spl_panic(\"C backend does not support async Spawn lowering\")")
expect(output).to_contain("spl_panic(\"C backend does not support actor Send lowering\")")
expect(output).to_contain("spl_panic(\"C backend does not support actor Receive lowering\")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/c_backend_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- C backend async lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
