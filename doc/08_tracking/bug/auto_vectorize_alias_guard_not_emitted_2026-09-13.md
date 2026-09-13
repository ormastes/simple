# Auto-vectorization is Active but rewrites almost nothing: the alias guard is not emitted

- **Status:** open — the remaining work after the 2026-09-13 `Active` flip
- **Where:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_alias.spl`,
  `_AutoVectorize/rewrite.spl` (`run_auto_vectorize`)

## Where things stand

`PassKind.AutoVectorize` is now `PassStatus.Active` (`mod.spl`), gated by the
alias oracle. The oracle is sound and complete for the question it is asked:

| base pair | verdict | pass behaviour |
|---|---|---|
| same local | `ExactAliasOnly` | **rewrites** |
| different, different proven origins | `ProvenDisjoint` | **rewrites** |
| different, same proven origin | `Unsafe` | refuses |
| either origin unproven | `NeedsRuntimeGuard` | **refuses** (today) |

The last row is the problem, and it is the common case: **MIR locals carry no
allocation identity**, so `origin_id` is `-1` for every base the rewriter sees.
Any loop whose output and inputs are different locals — i.e. essentially every
real `out[i] = a[i] + b[i]` — lands in `NeedsRuntimeGuard` and is refused.

So the pass is **active and sound, but fires only on the exact-alias shape**.
That is the correct trade (inert beats wrong), and it is deliberate: guessing
in the undecidable case is a silent miscompilation, which is the entire reason
the oracle exists.

## Why refusing is not permanent

Two independent unblocks, either of which makes the pass fire broadly:

**1. Emit the runtime range check.** `alias_guard_safe_at_runtime` already
states the predicate exactly, as a pure tested function:

```
safe  <=>  diff == 0  or  |diff| >= span_bytes
```

The unsafe window is the open interval `(0, span_bytes)` — a partial overlap at
a non-zero offset, the only arrangement where vector order differs from scalar
order. `MirBinOp` has `Sub`, `Eq`, `Ge`, `Le` and `BitOr`, and
`create_alignment_check_block` already demonstrates the branch-to-scalar block
shape, so this is expressible. What it needs that does not exist yet is a
**full-range scalar fallback block** to branch to: `create_peeling_block`
handles only the remainder, and the rewriter deletes the original loop body
rather than keeping a copy to version against.

**2. Thread allocation identity into MIR.** If a base local could report the
allocation it provably came from, `ProvenDisjoint` would cover the many loops
whose buffers are distinct locals from distinct allocation sites, with no
runtime cost at all. `AliasBase.origin_id` exists for exactly this and is
already honoured by the oracle — nothing in `auto_vectorize_alias.spl` needs to
change when a producer starts filling it in.

## Do not "fix" this by relaxing the oracle

Turning `NeedsRuntimeGuard` into "proceed anyway" would make the pass fire
broadly and silently miscompile any aliasing loop. The failure mode is a wrong
numeric answer in vectorized code, with no diagnostic and no crash — the
hardest class of bug to attribute. The refusal is the feature.

## Verification

- `auto_vectorize_alias_spec.spl` — 15/15, every verdict path plus a sweep of
  the runtime predicate across offsets `-64..64` asserting it refuses exactly
  the open window.
- `auto_vectorize_spec.spl` — 71/71, including the two Active-pass witnesses
  executed through `run_auto_vectorize`: distinct bases leave the function
  untouched, one shared base is admitted.
