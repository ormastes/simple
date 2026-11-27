# Loader Hot Swap: Identity Pin and Lockless Commit (RB-LOAD-01..02)

Status: minimal slice implemented 2026-11-23 — `src/compiler/99.loader/hot_swap_pin.spl`,
spec `test/01_unit/compiler/loader/hot_swap_pinning_spec.spl` (5/5, no longer in-development).
Remaining scope: `doc/08_tracking/todo/rb_load_hot_swap_pinning_2026-11-22.md`.

## Swap boundary

The unit of swap is one SMF library unit, identified by its SMF manifest row
(`SmfManifestEntry`). A `HotSwapSlot` holds:

- `pinned` — the manifest row the slot's dependents were built against
  (iface digest, ABI digest, target triple, policy, allowed capabilities). It is
  immutable for the slot's life; that is RB-LOAD-01.
- `generation` — an `AtomicI64` naming which published image is current.

The boundary is *image admission + generation commit*. Mapping segments
(`smf_segment_load.spl`), unload ownership (`unload_ownership.spl`,
`unload_policy.spl`) and source-triggered rebuild (`reload_rebuild.spl`) stay
where they are; they are the producer and the reclaim side of a swap and are not
wired to the slot yet (see todo).

## Identity check

`hot_swap_try(slot, observed, image)` calls
`smf_cached_unit_identity_admit(slot.pinned, image)` — the same function the
cold cached-SMF load path (`driver_api_interpret.try_load_smf_cached`, PR
#10908/#10926) uses. Hot-swap admission is therefore byte-identical to cold-load
admission: one authority, no second checker. Results:

| admit result | cold load | hot swap |
|---|---|---|
| `Ok(true)` | load | proceed to commit |
| `Err(SMF-E-UNIT-*)` (iface/ABI/triple/policy/capability) | refuse | refuse, generation unchanged |
| `Ok(false)` (legacy image, no identity record) | cache miss -> full interpret | **refuse** `SMF-E-UNIT-IDENTITY-MISSING` — a swap has no fallback |

## State migration

Not supported in this slice; refusal is the policy. Identical iface + ABI
digests mean every exported signature and data layout is unchanged, so live
state carries across by construction. Any digest difference is refused before
the commit point; nothing is half-applied. A migration hook (old-layout ->
new-layout transform, admitted against both ABI digests) is future work.

## Concurrency (lockless)

- Admission is pure (reads the immutable pin and the candidate bytes).
- The commit is one `compare_exchange(observed, observed + 1)` on the slot
  generation. Losing the CAS means another swap committed first: return
  `SMF-E-HOTSWAP-STALE`; the caller re-reads the generation, re-admits, and
  retries. No spin, no lock.
- The runtime atomic surface has I64/Usize/Bool only (no atomic pointer), so the
  generation token is the commit, and the generation -> image publication table
  is the caller's immutable value until the slot is wired into the production
  loader. Readers pin a generation and keep using that image until they drop it.
- `hot_swap_slot_new` fails closed (`SMF-E-HOTSWAP-ATOMIC`) if the atomic cannot
  be allocated. It uses `atomic_i64_try_new`: plain `atomic_i64_new` resolves to
  the i64-returning `io/debug_stubs.spl` twin under co-compilation in the
  interpreter (receiver becomes `i64`), recorded in the todo.
