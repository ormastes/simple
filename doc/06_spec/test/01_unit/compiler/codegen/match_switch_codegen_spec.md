# match_switch_codegen_spec

> B5 (compiler_bugs_for_crypto_2026-04-25.md) — verify dense `match` on

<!-- sdn-diagram:id=match_switch_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=match_switch_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

match_switch_codegen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=match_switch_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# match_switch_codegen_spec

B5 (compiler_bugs_for_crypto_2026-04-25.md) — verify dense `match` on

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/match_switch_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

B5 (compiler_bugs_for_crypto_2026-04-25.md) — verify dense `match` on
integer constants lowers to a MIR `Terminator::Switch`, which Cranelift
emits as `br_table`.

Acceptance gates the TLS-1.3 cipher dispatcher: a 5+ arm match on cipher_id
with span ≤ 1024 must dispatch in ≤ 2× direct-call cost. We can't observe
the IR shape from Simple, so we exercise the dispatch correctness for every
arm; the IR-shape assertion lives next to the codegen impl.

## Scenarios

### match-on-int dispatch (B5)

#### arm 0 returns 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch(0)).to_equal(100)
```

</details>

#### arm 1 returns 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch(1)).to_equal(200)
```

</details>

#### arm 2 returns 300

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch(2)).to_equal(300)
```

</details>

#### arm 3 returns 400

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch(3)).to_equal(400)
```

</details>

#### arm 4 returns 500

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch(4)).to_equal(500)
```

</details>

#### default arm returns -1 for out-of-range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dispatch(5)).to_equal(-1)
expect(dispatch(-1)).to_equal(-1)
expect(dispatch(1000)).to_equal(-1)
```

</details>

#### sparse non-dense match still works (falls back to if-chain)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = match 7:
    case 7: 99
    case _: 0
expect(r).to_equal(99)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
