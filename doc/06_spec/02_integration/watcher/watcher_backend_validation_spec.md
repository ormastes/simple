# watcher_backend_validation_spec

> Watcher Backend Validation Specification

<!-- sdn-diagram:id=watcher_backend_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_backend_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_backend_validation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_backend_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_backend_validation_spec

Watcher Backend Validation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-INT-021 to #WATCH-INT-030 |
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/watcher/watcher_backend_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher Backend Validation Specification

Tests that compiling with one backend and loading with another
is properly detected and handled.

## Scenarios

### Backend Validation

### matching backends

<details>
<summary>Advanced: LLVM compiled, LLVM loaded</summary>

#### LLVM compiled, LLVM loaded _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `ok`
   - Expected: ldr_warnings_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val hash = mock_compute("llvm", 2, true)
ldr_store("main.smf", hash)
val result = ldr_load_validated("main.smf", hash)
expect(result).to_equal("ok")
expect(ldr_warnings_len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: Cranelift compiled, Cranelift loaded</summary>

#### Cranelift compiled, Cranelift loaded _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `ok`
   - Expected: ldr_warnings_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val hash = mock_compute("cranelift", 1, false)
ldr_store("main.smf", hash)
val result = ldr_load_validated("main.smf", hash)
expect(result).to_equal("ok")
expect(ldr_warnings_len()).to_equal(0)
```

</details>


</details>

### mismatching backends

<details>
<summary>Advanced: LLVM compiled, Cranelift loaded warns</summary>

#### LLVM compiled, Cranelift loaded warns _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `mismatch`
   - Expected: ldr_warnings_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val llvm_hash = mock_compute("llvm", 2, true)
val crank_hash = mock_compute("cranelift", 2, true)
ldr_store("main.smf", llvm_hash)
val result = ldr_load_validated("main.smf", crank_hash)
expect(result).to_equal("mismatch")
expect(ldr_warnings_len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: Cranelift compiled, LLVM loaded warns</summary>

#### Cranelift compiled, LLVM loaded warns _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `mismatch`
   - Expected: ldr_warnings_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val crank_hash = mock_compute("cranelift", 1, false)
val llvm_hash = mock_compute("llvm", 1, false)
ldr_store("main.smf", crank_hash)
val result = ldr_load_validated("main.smf", llvm_hash)
expect(result).to_equal("mismatch")
expect(ldr_warnings_len()).to_equal(1)
```

</details>


</details>

### opt level mismatch

<details>
<summary>Advanced: different opt levels detected</summary>

#### different opt levels detected _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `mismatch`
   - Expected: ldr_warnings_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val hash_o0 = mock_compute("llvm", 0, false)
val hash_o3 = mock_compute("llvm", 3, false)
ldr_store("main.smf", hash_o0)
val result = ldr_load_validated("main.smf", hash_o3)
expect(result).to_equal("mismatch")
expect(ldr_warnings_len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: same opt level is ok</summary>

#### same opt level is ok _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val hash = mock_compute("llvm", 2, false)
ldr_store("main.smf", hash)
val result = ldr_load_validated("main.smf", hash)
expect(result).to_equal("ok")
```

</details>


</details>

### release flag mismatch

<details>
<summary>Advanced: debug vs release detected</summary>

#### debug vs release detected _(slow)_

1. ldr reset
2. ldr store
   - Expected: result equals `mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val debug_hash = mock_compute("llvm", 2, false)
val release_hash = mock_compute("llvm", 2, true)
ldr_store("main.smf", debug_hash)
val result = ldr_load_validated("main.smf", release_hash)
expect(result).to_equal("mismatch")
```

</details>


</details>

### missing module

<details>
<summary>Advanced: reports missing for unloaded module</summary>

#### reports missing for unloaded module _(slow)_

1. ldr reset
   - Expected: result equals `missing`
   - Expected: ldr_warnings_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ldr_reset()
val hash = mock_compute("llvm", 2, true)
val result = ldr_load_validated("nonexistent.smf", hash)
expect(result).to_equal("missing")
expect(ldr_warnings_len()).to_equal(0)
```

</details>


</details>

### hash stability

<details>
<summary>Advanced: same options always produce same hash</summary>

#### same options always produce same hash _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = mock_compute("cranelift", 2, true)
val h2 = mock_compute("cranelift", 2, true)
expect(h1).to_equal(h2)
```

</details>


</details>

<details>
<summary>Advanced: different options produce different hashes</summary>

#### different options produce different hashes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = mock_compute("llvm", 2, true)
val h2 = mock_compute("cranelift", 2, true)
expect(h1 != h2).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
