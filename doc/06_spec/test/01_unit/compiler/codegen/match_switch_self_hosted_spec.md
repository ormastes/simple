# match_switch_self_hosted_spec

> B5b — self-hosted compiler MIR lowering of `MatchCase`.

<!-- sdn-diagram:id=match_switch_self_hosted_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=match_switch_self_hosted_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

match_switch_self_hosted_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=match_switch_self_hosted_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# match_switch_self_hosted_spec

B5b — self-hosted compiler MIR lowering of `MatchCase`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/match_switch_self_hosted_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

B5b — self-hosted compiler MIR lowering of `MatchCase`.

Verifies the self-hosted (Simple-written) MIR lowerer in
`src/compiler/50.mir/mir_lowering_expr.spl` correctly lowers
integer-literal `match` expressions to:

  - `MirTerminator.Switch` for dense (>=4 arms, span <= 1024) cases
    so backends emit a jump table.
  - Nested `If` chain for sparse / smaller cases.

Phase 1 scope:
  - Wildcard default arm
  - Literal(IntLit n) arms

Phase 2a scope (added in this spec):
  - Binding pattern (`case x:`) — irrefutable default that also binds
    the scrutinee to a local symbol
  - Or pattern with all-IntLit alternatives (`case 1 | 2 | 3:`) —
    each alternative becomes its own dispatch entry pointing at the
    shared arm body

Phase 2b (still NOT in scope; documented in
`doc/08_tracking/todo/compiler_bugs_for_crypto_2026-04-25.md` §B5b):
  - Tuple, Array, Struct, Enum, Range patterns
  - Or with non-IntLit alternatives
  - Non-IntLit Literal (Bool/Char/String)
  - Match-arm guards
  - Result type merging across non-uniform arm bodies
  - Exhaustiveness for matches without wildcard/binding default

The companion sibling spec `match_switch_codegen_spec.spl` already
covers the Rust-seed B5 path; this spec exercises the same shapes
through the self-hosted release binary so the deliberate-fail probe
is a real signal of self-hosted MIR-lowering correctness.

## Scenarios

### B5b · self-hosted MatchCase MIR lowering

#### dense dispatch hits each arm correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dense_dispatch(0)).to_equal(100)
expect(dense_dispatch(1)).to_equal(200)
expect(dense_dispatch(2)).to_equal(300)
expect(dense_dispatch(3)).to_equal(400)
expect(dense_dispatch(4)).to_equal(500)
```

</details>

#### dense dispatch wildcard returns -1 for out-of-range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dense_dispatch(5)).to_equal(-1)
expect(dense_dispatch(-1)).to_equal(-1)
expect(dense_dispatch(1000)).to_equal(-1)
```

</details>

#### sparse dispatch (2 arms) still works via if-chain fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sparse_dispatch(7)).to_equal(99)
expect(sparse_dispatch(8)).to_equal(0)
expect(sparse_dispatch(0)).to_equal(0)
```

</details>

#### wide-span dispatch (span > 1024) still works via if-chain fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wide_span_dispatch(0)).to_equal(1)
expect(wide_span_dispatch(1000)).to_equal(2)
expect(wide_span_dispatch(2000)).to_equal(3)
expect(wide_span_dispatch(500)).to_equal(0)
```

</details>

#### TLS-shape cipher dispatcher returns correct id per arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_lookup(0xC02F)).to_equal(1)
expect(cipher_lookup(0xC030)).to_equal(2)
expect(cipher_lookup(0xCCA8)).to_equal(3)
expect(cipher_lookup(0x1301)).to_equal(4)
expect(cipher_lookup(0x1302)).to_equal(5)
expect(cipher_lookup(0x1303)).to_equal(6)
expect(cipher_lookup(0x1304)).to_equal(7)
expect(cipher_lookup(0x9999)).to_equal(0)
```

</details>

#### Phase 2a binding pattern: int arms route to int branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binding_default(1)).to_equal(100)
expect(binding_default(2)).to_equal(200)
```

</details>

#### Phase 2a binding pattern: default arm uses bound symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binding_default(5)).to_equal(1005)
expect(binding_default(-3)).to_equal(997)
expect(binding_default(0)).to_equal(1000)
```

</details>

#### Phase 2a binding-only match (default arm is sole arm)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(binding_only(0)).to_equal(0)
expect(binding_only(7)).to_equal(14)
expect(binding_only(-4)).to_equal(-8)
```

</details>

#### Phase 2a Or-of-IntLit dense routes through Switch

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(or_dense(1)).to_equal(10)
expect(or_dense(2)).to_equal(10)
expect(or_dense(3)).to_equal(10)
expect(or_dense(4)).to_equal(20)
expect(or_dense(5)).to_equal(30)
expect(or_dense(0)).to_equal(0)
expect(or_dense(99)).to_equal(0)
```

</details>

#### Phase 2a Or-of-IntLit sparse routes through if-chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(or_sparse(7)).to_equal(99)
expect(or_sparse(11)).to_equal(99)
expect(or_sparse(8)).to_equal(0)
expect(or_sparse(0)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
