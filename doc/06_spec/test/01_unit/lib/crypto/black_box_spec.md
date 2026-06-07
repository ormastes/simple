# black_box_spec

> B6 (compiler_bugs_for_crypto_2026-04-25.md) — `black_box` opaque

<!-- sdn-diagram:id=black_box_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=black_box_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

black_box_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=black_box_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# black_box_spec

B6 (compiler_bugs_for_crypto_2026-04-25.md) — `black_box` opaque

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/black_box_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

B6 (compiler_bugs_for_crypto_2026-04-25.md) — `black_box` opaque
identity intrinsic.

Wraps an integer through an external function call so Cranelift /
optimizers can't see through it. Used to keep XOR-accumulate
constant-time compare loops from being rewritten into early-exit
branches on `diff != 0`.

Cranelift IR shape ("no `brif diff` in the inner loop") is verified
**by construction**: extern function calls are opaque to Cranelift's
optimizer by design. This spec verifies functional correctness only.

## Scenarios

### black_box (B6)

#### is identity on integer inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(black_box(0)).to_equal(0)
expect(black_box(42)).to_equal(42)
expect(black_box(-1)).to_equal(-1)
```

</details>

#### ct_eq_bytes returns true for equal buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1u8, 2u8, 3u8, 4u8]
val b = [1u8, 2u8, 3u8, 4u8]
expect(ct_eq_bytes(a, b)).to_equal(true)
```

</details>

#### ct_eq_bytes returns false on byte difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1u8, 2u8, 3u8, 4u8]
val b = [1u8, 2u8, 3u8, 5u8]
expect(ct_eq_bytes(a, b)).to_equal(false)
```

</details>

#### ct_eq_bytes returns false on length difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1u8, 2u8, 3u8]
val b = [1u8, 2u8, 3u8, 4u8]
expect(ct_eq_bytes(a, b)).to_equal(false)
```

</details>

#### ct_eq_bytes handles empty buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(ct_eq_bytes(empty, empty)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
