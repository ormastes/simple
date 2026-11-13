# Four new single-lane `rt_vulkan_*` symbols block every push
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN — blocks the `push-rt-dual-implementation` BLOCKING gate for all sessions
**Found:** 2026-09-05, while pushing an unrelated lane

## Symptom

```
$ sh scripts/check/check-rt-dual-implementation-ratchet.shs
FAIL — 2492 symbol(s) checked against 2488 baselined, 4 new, 0 stale
  ... rt_vulkan_copy_u32_slots
      rt_vulkan_readback_u32_checksum
```

`push-rt-dual-implementation` is a **blocking** push-tier row
(`config/check/must_check_gates.sdn:21`), so this fails every `git push` from
this repository regardless of what the pushing lane changed. It is tree-scoped,
not range-scoped.

## Not the pushing lane's doing

Reproduced on the untouched main working tree (same verdict, same four symbols),
and on a cherry-pick range that touches no `.c`, `.rs`, or runtime file at all.
The failure is inherited from committed content, not introduced by a push.

## What is actually missing (measured, not assumed)

The four symbols are NOT absent everywhere. `rt_vulkan_copy_u32_slots`, for
example, exists in three places:

```
src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:571  pub extern "C" fn rt_vulkan_copy_u32_slots(
src/compiler_rust/compiler/src/interpreter_extern/vulkan.rs:165      ("rt_vulkan_copy_u32_slots", Ret::I, "vvi"),
src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:83                extern fn rt_vulkan_copy_u32_slots(...)
```

So there is a Rust implementation, an interpreter extern registration, and a
Simple declaration. What is missing is the **C lane** — which is precisely the
axis `check-rt-dual-implementation-ratchet.shs` measures. A reader who greps for
the symbol will find it and conclude the gate is wrong; it is not.

## Why the baseline must NOT simply be regenerated

The guard's contract is that an `rt_*` symbol exists in BOTH the C and Simple
lanes. A symbol implemented in Rust but not C is exactly the gap the ratchet
exists to catch. Running `--generate-baseline` would record the single-lane state as
accepted debt and launder exactly what was caught — the same anti-pattern
`.claude/rules/vcs.md` warns about for the divergence and unbacked-extern
ratchets.

The correct fix is one of:
- implement the missing lane for all four symbols, or
- remove them if the lane that added them no longer needs them, or
- a reviewed, deliberate baseline update by **the lane that added them**, with the
  reason recorded.

Whoever added the `rt_vulkan_*` work owns this call. It is not a decision an
unrelated lane should make by regenerating a baseline to unblock itself.

## Interim

Until it is resolved, every push from this repo either fails or is forced with
`--no-verify`, which nullifies all 18 push-tier gates rather than just this one.
That is a much worse state than one red gate, and is the reason this record
exists rather than a silent workaround.



---

## 2026-11-13 addendum — P3 gpu lane p3-gpu-20261113 (work/p3-gpu-20261113, base 6f4cb189867) — header flip: FIXED at tip

**Verdict: FIXED (resolved 2026-09-06 by the owning lane; this addendum flips the
stale header with tip evidence).** The record's own three correct options were
followed — the missing C lane was implemented for the symbols, with the
reviewed baseline update recorded inline:

- `scripts/check/rt_dual_implementation_baseline.txt` header notes (verbatim at
  tip): "2026-09-06, reviewed addition of FOUR rows that origin/main already
  carries single-lane ... rt_vulkan_copy_u32_slots and rt_vulkan_readback_u32_checksum
  (rust-only, 320e6d99e4b 09-05). Recorded as pre-existing debt, not accepted as
  new" — followed the same day by "chain-4 landing (merge f5ac48658d2 ...): THREE
  rows deleted because the merge gives each its missing lane — verified
  individually in the merged tree": `rt_vulkan_copy_u32_slots` gained a C twin at
  `src/runtime/runtime_native.c:7239` (now :10912 at this tip) and
  `rt_vulkan_readback_u32_checksum` at `src/runtime/runtime_native.c:397` (now
  :461); the Rust lanes remain at
  `src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:571`/`:464`.
- Source re-verified at this base: both C twins are present and non-static
  (`grep` confirmed at the lines above); the two symbols are no longer listed as
  `rust-only` rows in the committed baseline (only the historical header notes
  mention them). The fourth symbol of the original four-row failure
  (`rt_to_int_dynamic`, c-only) received its Rust lane in the same chain-4 merge
  per the same note; `rt_phase_profile_record` was handled with an explicit
  guard-visibility explanation in the same baseline header.
- The ratchet itself (`check-rt-dual-implementation-ratchet.shs`) runs `nm`
  against the deployed Linux binary and cannot execute on this Windows lane, so
  no fresh gate run was performed; the in-source dual-lane evidence plus the
  reviewed baseline history above is the flip basis, consistent with this
  record's "verified individually in the merged tree" standard.
