# CUDA Backend

> Real CUDA backend checks through the Simple `std.nogc_async_mut.cuda` surface.

<!-- sdn-diagram:id=cuda_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA Backend

Real CUDA backend checks through the Simple `std.nogc_async_mut.cuda` surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/cuda_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Real CUDA backend checks through the Simple `std.nogc_async_mut.cuda` surface.
These tests run against the compiled runtime rather than stub helpers.

## Scenarios

### CUDA runtime surface

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### reports an internally consistent availability state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = cuda.cuda_available()
val count = cuda.cuda_device_count()

if available:
    expect(count).to_be_greater_than(0)
else:
    expect(count).to_equal(0)
```

</details>

#### returns a stable init result

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_rc = cuda.cuda_init()
val available = cuda.cuda_available()
val count = cuda.cuda_device_count()

if available:
    expect(init_rc).to_equal(cuda.CUDA_SUCCESS)
    expect(count).to_be_greater_than(0)
else:
    expect(count).to_equal(0)
    expect(init_rc == cuda.CUDA_SUCCESS or init_rc == cuda.CUDA_ERROR_NOT_INITIALIZED or init_rc == cuda.CUDA_ERROR_NO_DEVICE).to_equal(true)
```

</details>

#### reports device metadata when CUDA is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if cuda.cuda_available():
    val device = cuda.cuda_device_get(0)
    val name = cuda.cuda_device_name(device)
    val cc = cuda.cuda_device_compute_capability(device)
    expect(device).to_be_greater_than(-1)
    expect(name.len()).to_be_greater_than(0)
    expect(cc).to_be_greater_than(0)
else:
    expect(cuda.cuda_device_count()).to_equal(0)
```

</details>

#### maps known error codes to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = cuda.cuda_get_error_string(cuda.CUDA_ERROR_NOT_INITIALIZED)
# When CUDA is compiled in, the message contains "NOT_INITIALIZED".
# When CUDA support is disabled in the runtime, the stub returns a
# fixed "CUDA support disabled" string instead.
val has_info = msg.contains("NOT_INITIALIZED") or msg.contains("CUDA support disabled")
expect(has_info).to_equal(true)
```

</details>

#### rejects invalid PTX when CUDA is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = cuda.cuda_module_load_data(invalid_ptx())
if cuda.cuda_available():
    expect(module).to_be_less_than(0)
else:
    expect(module).to_equal(cuda.CUDA_ERROR_NOT_INITIALIZED)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
