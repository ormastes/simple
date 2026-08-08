# Lane FV2 — Formal Enforcement Invariants (master plan §21.3)

Status: **COMPLETE — sorry-free, gate GREEN.**
Date: 2026-07-27

Three core-Lean-4 proof modules (no Mathlib, offline manifest) modelling REAL
invariants from landed SimpleOS enforcement code. All theorems close sorry-free.

## Gate command + result

```
cd src/verification/os_enforcement && lake build
```
Result: `Build completed successfully (6 jobs).` — EXIT 0, ZERO errors, ZERO
`sorry`/`admit`. `grep -nE '\b(sorry|admit)\b'` matches ONLY the three
"sorry-free" comment strings in the module headers (count of real occurrences = 0).

Axiom audit (`#print axioms` on one+ theorem per module) — no `sorryAx` anywhere:
- ContainerIsolation: `rootless_denies_all` / `traversal_cannot_escape` —
  "does not depend on any axioms".
- DeviceGrant: `revoke_independence`, `no_dma_without_iommu` — `[propext, Quot.sound]`.
- ProfileAttenuation: `effective_subset_ceilings`, `deny_wins`,
  `spawn_triple_attenuation` — `[propext, Quot.sound]`.
(`propext`/`Quot.sound` are the standard axioms pulled in by core `List` lemmas —
NOT sorryAx.)

## Files (exclusive paths, working copy only — NOT committed)

- src/verification/os_enforcement/OsEnforcement/ContainerIsolation.lean (new)
- src/verification/os_enforcement/OsEnforcement/DeviceGrant.lean (new)
- src/verification/os_enforcement/OsEnforcement/ProfileAttenuation.lean (new)
- (root OsEnforcement.lean / lakefile / manifest UNCHANGED — all 3 imports kept.)

## Module 1 — ContainerIsolation.lean

Models `src/os/kernel/loader/container_namespace.spl`
(`ContainerNamespaceView`, `container_view_allows_path/_pid`, `_split_components`).

Model:
- View = (root : List Nat components, pids : List Nat). Path segments abstracted
  as Nat ids. `..` modelled by sentinel `DOTDOT = 0`.
- `prefixB root path` = component-wise prefix (recursive; mirrors the `req[i] !=
  root[i]` loop + `req.len < root.len` early-deny; NOT string starts_with).
- `allowsPath root path` = `[] => false` (rootless/empty root denies all) else
  `prefixB root path`.
- `allowsPid pids p` = `pids.contains p`.
- `normalize` (via `normAux` accumulator) mirrors `_split_components`: collapses
  "." implicitly, drops last accumulated component on `..`, returns `none` when
  `..` pops above the empty accumulator (the nil / DENY signal).
- `pathDecision root path` = `none => false` else `allowsPath root (normalized)`.

Theorems proved (all closed):
- **CI1 rootless_denies_all** — `allowsPath [] path = false ∧ allowsPid [] p = false`.
- **CI2 outside_root_denied** — `prefixB (a::as) path = false → allowsPath (a::as) path = false`;
  plus concrete `outside_root_denied_sibling`: root `[1]` denies sibling `[11]`
  (the "/c1 vs /c11" starts_with trap the source avoids).
- **CI3 traversal_cannot_escape** — general: `normalize path = some np →
  prefixB root np = false → pathDecision root path = false`; `traversal_escape_denied`:
  `normalize path = none → pathDecision = false`; concrete
  `traversal_cannot_escape_concrete`: under `[1]`, `[1,DOTDOT,2]` normalizes to
  `[2]` and is denied, and `[DOTDOT]` (pop above fs root) is denied.
- **CI4 pid_outside_set_denied** — `¬ p ∈ pids → allowsPid pids p = false`.

## Module 2 — DeviceGrant.lean

Models `src/os/drivers/device_grant.spl` + `device_grant_revocation.spl`
(`grant_has`/`grant_revoke`, `revocation_can_advance`/`_apply_effect`/
`_can_acquire_dma`).

Model:
- Rights = `List Nat` set of held right-ids (bit values BAR=1..IOMMU=32 kept as
  distinct atoms). `has rs r` = `rs.contains r` (mirrors grant_has single-bit).
  `revoke rs r` = `rs.filter (· != r)` (mirrors grant_revoke: clear exactly r).
- `Seq {currentStep, rights}`; `canAdvance s step` = `step == current+1 && step ≤ 10`;
  `applyEffect` (step 3 clears DMA, step 4 clears IOMMU, step 6 clears
  BAR|IOPORT|IRQ|MSI); `advance` = unchanged unless canAdvance.
- `canAcquireDma rs` = `has rs DMA && has rs IOMMU`.

Theorems proved (all closed):
- **DG1 revoke_independence** — `has rs BAR ∧ has rs IRQ → has (revoke rs DMA) BAR
  ∧ has (revoke rs DMA) IRQ` (independent bits: revoking DMA leaves BAR, IRQ).
- **DG2 ordering_no_skip** — `step ≠ current+1 → advance s step = s` (out-of-order
  advance rejected, sequence unchanged).
- **DG3 no_dma_without_iommu** — `canAcquireDma (applyEffect rs 3) = false` (after
  the DMA-revoke step, DMA right gone ⇒ cannot DMA); plus corollary
  `no_dma_after_iommu_removed`: `canAcquireDma (applyEffect rs 4) = false` (IOMMU
  removed at step 4).

## Module 3 — ProfileAttenuation.lean

Models `src/os/security/llm_profiles/profile_registry.spl` `resolve_effective` +
`profile_spawn_adapter.spl` `llm_spawn_effective_rights`.

Model:
- Rights = `List Nat` set (Nat bitmask). `inter` = filter present-in-both (`&`);
  `diff` = filter not-in-b (`& ~b`, the unconditional deny subtraction);
  `granted` = foldl append base+overlays (the only union). `Sub` = set inclusion.
- `resolveEffective base overlays sys user denies` =
  `diff (inter (inter (granted base overlays) sys) user) denies`
  (union base+overlays → intersect BOTH ceilings → subtract denies LAST).
- `spawnRights profileR parentDeleg execCeil` =
  `inter (inter profileR parentDeleg) execCeil` (pure triple intersection).

Theorems proved (all closed):
- **PA1 effective_subset_ceilings** — effective ⊆ sys ∧ effective ⊆ user.
- **PA2 deny_wins** — `r ∈ denies → ¬ r ∈ resolveEffective …` (deny subtracted
  last & unconditionally, beats any base/overlay grant).
- **PA3 spawn_triple_attenuation** — spawnRights ⊆ profileR ∧ ⊆ parentDeleg ∧ ⊆
  execCeil (never amplified beyond any of the three inputs).

## Blocked rows

NONE. All 4 CI + 3 DG + 3 PA headline invariants closed sorry-free (plus 4
supporting corollaries). No theorem was dropped; no import removed from the root.

## Resume / re-verify command

```
cd /home/ormastes/dev/pub/simple/src/verification/os_enforcement && lake build
grep -nE '\b(sorry|admit)\b' OsEnforcement/*.lean   # only comment strings expected
```
