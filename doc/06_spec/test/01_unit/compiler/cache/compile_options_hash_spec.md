# compile_options_hash_spec

> CompileOptionsHash Specification

<!-- sdn-diagram:id=compile_options_hash_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compile_options_hash_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compile_options_hash_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compile_options_hash_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# compile_options_hash_spec

CompileOptionsHash Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CACHE-011 to #CACHE-020 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/cache/compile_options_hash_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

CompileOptionsHash Specification

Tests hash computation, validation, and serialization roundtrip
for compile options stored in SMF headers.

## Scenarios

### CompileOptionsHash

### computation

#### produces non-zero hash for valid options

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_compute("llvm", 2, true, true, false)
expect(h.hash != 0).to_equal(true)
expect(h.backend_kind).to_equal(1)
expect(h.opt_level).to_equal(2)
```

</details>

#### different backends produce different hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = options_hash_compute("llvm", 2, true, true, false)
val h2 = options_hash_compute("cranelift", 2, true, true, false)
expect(h1.hash != h2.hash).to_equal(true)
expect(h1.backend_kind).to_equal(1)
expect(h2.backend_kind).to_equal(2)
```

</details>

#### normalizes llvm-lib aliases to the llvm backend kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = options_hash_compute("llvm-lib", 2, true, true, false)
val h2 = options_hash_compute("llvmlib", 2, true, true, false)
val h3 = options_hash_compute("llvm", 2, true, true, false)
expect(h1.backend_kind).to_equal(1)
expect(h2.backend_kind).to_equal(1)
expect(h1.hash).to_equal(h3.hash)
expect(h2.hash).to_equal(h3.hash)
```

</details>

#### different opt levels produce different hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = options_hash_compute("llvm", 0, false, true, false)
val h2 = options_hash_compute("llvm", 3, false, true, false)
expect(h1.hash != h2.hash).to_equal(true)
```

</details>

#### same options produce same hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = options_hash_compute("cranelift", 1, false, true, false)
val h2 = options_hash_compute("cranelift", 1, false, true, false)
expect(h1.hash).to_equal(h2.hash)
expect(h1.backend_kind).to_equal(h2.backend_kind)
```

</details>

#### clamps opt level to 0..3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = options_hash_compute("llvm", -5, false, false, false)
val h2 = options_hash_compute("llvm", 99, false, false, false)
expect(h1.opt_level).to_equal(0)
expect(h2.opt_level).to_equal(3)
```

</details>

### flags

#### sets debug_info flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_compute("auto", 0, false, true, false)
expect(h.flags).to_equal(1)
```

</details>

#### sets gc_off flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_compute("auto", 0, false, false, true)
expect(h.flags).to_equal(2)
```

</details>

#### sets release flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_compute("auto", 0, true, false, false)
expect(h.flags).to_equal(4)
```

</details>

#### combines flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_compute("auto", 0, true, true, true)
expect(h.flags).to_equal(7)
```

</details>

### zero

#### creates zero hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_zero()
expect(options_hash_is_zero(h)).to_equal(true)
```

</details>

#### computed hash is not zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = options_hash_compute("llvm", 2, true, true, false)
expect(options_hash_is_zero(h)).to_equal(false)
```

</details>

### serialization roundtrip

#### roundtrips through bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = options_hash_compute("cranelift", 2, true, true, false)
val bytes = options_to_bytes(original)
val restored = options_from_bytes(bytes)
expect(restored.hash).to_equal(original.hash)
expect(restored.backend_kind).to_equal(original.backend_kind)
expect(restored.opt_level).to_equal(original.opt_level)
expect(restored.flags).to_equal(original.flags)
```

</details>

#### handles empty bytes as zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val restored = options_from_bytes([])
expect(options_hash_is_zero(restored)).to_equal(true)
```

</details>

### validation

#### matching hashes validate as fresh

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stored = options_hash_compute("llvm", 2, true, true, false)
val current = options_hash_compute("llvm", 2, true, true, false)
expect(stored.hash).to_equal(current.hash)
expect(stored.backend_kind).to_equal(current.backend_kind)
```

</details>

#### different backends are detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stored = options_hash_compute("llvm", 2, true, true, false)
val current = options_hash_compute("cranelift", 2, true, true, false)
expect(stored.hash != current.hash).to_equal(true)
expect(stored.backend_kind != current.backend_kind).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
