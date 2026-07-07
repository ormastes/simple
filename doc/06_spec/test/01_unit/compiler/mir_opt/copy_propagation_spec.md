# CopyPropagation Specification

> Validates the CopyPropagation pass which promotes copy-to-move when the source register has no subsequent uses, and propagates through chains of copies back to the original source.

<!-- sdn-diagram:id=copy_propagation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=copy_propagation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

copy_propagation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=copy_propagation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CopyPropagation Specification

Validates the CopyPropagation pass which promotes copy-to-move when the source register has no subsequent uses, and propagates through chains of copies back to the original source.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | Compiler / MIR Optimization |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/compiler/mir_opt/copy_propagation_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the CopyPropagation pass which promotes copy-to-move when the
source register has no subsequent uses, and propagates through chains of
copies back to the original source.

## Behavior

- Source with no subsequent uses → copy promoted to move
- Source used after the copy → copy preserved
- Chain of copies resolved to original source
- Pass statistics count every promoted copy

## Scenarios

### CopyPropagation

### copy-to-move promotion

#### promotes copy to move when source has no subsequent uses

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# %src is defined at pos 0, copied at pos 5, never used after pos 5.
val src_uses = [0, 5]
val copy_pos = 5
val uses_after = use_count_after(src_uses, copy_pos)
val should_promote = can_promote_to_move(uses_after)
expect(should_promote).to_equal(true)
```

</details>

#### preserves copy when source is used after copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# %src is used at pos 7, copied at pos 5 — use comes after copy.
val src_uses = [0, 5, 7]
val copy_pos = 5
val uses_after = use_count_after(src_uses, copy_pos)
val should_promote = can_promote_to_move(uses_after)
expect(should_promote).to_equal(false)
```

</details>

### chain propagation

#### handles chain of copies — propagates through to original source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# %a → %b → %c → %d: original source is %a
val chain = ["%a", "%b", "%c", "%d"]
val original = resolve_copy_chain(chain)
expect(original).to_equal("%a")
```

</details>

#### returns sole element as source for length-1 chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chain = ["%x"]
val original = resolve_copy_chain(chain)
expect(original).to_equal("%x")
```

</details>

### pass statistics

#### counts promoted copies in pass statistics

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4 copies: first 3 promotable, last one is not.
val copies = ["%a", "%b", "%c", "%d"]
val moveable = [true, true, true, false]
val promoted = simulate_copy_promotion(copies, moveable)
expect(promoted).to_equal(3)
expect(promoted).to_be_greater_than(0)
```

</details>

#### reports zero promoted copies when none qualify

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val copies = ["%x", "%y"]
val moveable = [false, false]
val promoted = simulate_copy_promotion(copies, moveable)
expect(promoted).to_equal(0)
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
