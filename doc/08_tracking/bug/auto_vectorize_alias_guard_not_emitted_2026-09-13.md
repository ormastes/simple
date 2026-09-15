# Auto-vectorization is Active but rewrites almost nothing: the alias guard is not emitted

- **Status:** RESOLVED 2026-09-13 — the guard is emitted and the pass fires
  end to end. The analysis below is retained because the chain of blockers it
  describes is instructive.
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

## Resolved — and the real last blocker was not the guard

The runtime range check is now emitted (`create_alias_guard_block`), backed by a
full-range scalar clone (`create_scalar_version_block`), and
`NeedsRuntimeGuard` takes that path instead of refusing.

But emitting it was not sufficient, and the reason is worth recording. Two
further defects sat underneath, each of which independently made the pass
incapable of transforming anything:

**1. `detect_loop_bounds` hardcoded `end_value = -1`.** Even when the upper
operand was a literal constant, the comment said the value could not be
determined "without deeper inspection" — while the value was sitting in the
operand. Because the rewriter's R4 refuses a dynamic trip count, that single
`-1` refused EVERY loop, regardless of what the pattern matcher or the alias
oracle decided. Fixed by reading the constant.

**2. The unit fixtures were not realistic loops.** `detect_array_accesses`
recovers base arrays from `GetElementPtr` instructions; the fixtures used bare
`Load(dest, ptr)` with no GEP, so `input_bases` came back empty and
`output_base` nil, and R5/R6 refused. Real loop bodies address arrays through
GEPs. A GEP-indexed fixture was added, and with it the pass transforms.

The order matters for anyone retracing this: the alias oracle was never what
stopped the pass. It was the last gate reached, so it looked like the blocker,
but two earlier gates were refusing everything before the oracle was consulted.

## Now verified end to end

`auto_vectorize_spec.spl` — 80/80, including:

- a constant-bounded GEP-indexed `out[i] = a[i] + b[i]` that the pass actually
  transforms through `run_auto_vectorize`;
- `alias_check` and `scalar_version` blocks present for distinct bases;
- **no** guard emitted when every base is the same local, since an exact alias
  is proven safe statically and a runtime check there would be dead weight;
- a genuinely dynamic upper bound still refused;
- the guard block carrying exactly 6 comparison instructions per input base
  plus the combining AND, and refusing to emit at all when the element width is
  unknown (an unbounded guard admits everything, which is worse than not
  vectorizing).
