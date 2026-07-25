# Lane HARDEN-SEC — Recovery Manifest

Adversarial hardening of the SimpleOS OCap security core. All specs verified with
`src/compiler_rust/target/release/simple run <spec>` (interpreter path executes
`it` assertions — confirmed via a control assertion).

## New adversarial spec files (test-only)
- `test/01_unit/os/security/adversarial_escalation_attenuation_spec.spl`  (20 examples GREEN)
- `test/01_unit/os/security/adversarial_revocation_soundness_spec.spl`     (5 examples GREEN)
- `test/01_unit/os/security/adversarial_sealed_confusion_spec.spl`         (19 examples GREEN)

Total new: 44 examples, 0 failures.

## REAL fail-OPEN bug FOUND + FIXED (root cause)

File: `src/os/kernel/ipc/capability.spl`, method `CapabilityManager.create_child_session`.

Bug: containment used `capset_subset(ceiling, parent.current)`. `capset_subset`
(session_types.spl) iterates only the SUB set's concrete tokens. An ambient-full
CapabilitySet (`is_pledged:false` + zero tokens = `CapabilitySet.full()`) has NO
tokens to iterate, so it VACUOUSLY passed containment. Result: a caller could
mint a child session whose `current` authorizes everything a NARROW parent did
NOT — a session-authority privilege escalation (child minted ABOVE its parent).

Proven empirically: before the fix, `create_child_session(root_with_narrow_caps,
ceiling=full(), current=full())` returned a non-nil child.

Minimal root fix (in create_child_session, my permitted file) — insert BEFORE the
two `capset_subset` checks:

```
        # SECURITY (fail-closed): an ambient-full set (is_pledged:false + zero
        # tokens) represents ALL authority, but capset_subset only iterates its
        # (empty) token list and would VACUOUSLY pass containment — minting a
        # child ABOVE its parent (a session-authority escalation). Guard it
        # explicitly: an ambient ceiling is contained only by an ambient parent,
        # and an ambient current only by an ambient ceiling.
        val ceiling_ambient = (not ceiling.is_pledged) and (ceiling.caps.len() == 0)
        val parent_ambient = (not parent.current.is_pledged) and (parent.current.caps.len() == 0)
        if ceiling_ambient and (not parent_ambient):
            return nil
        val current_ambient = (not current.is_pledged) and (current.caps.len() == 0)
        if current_ambient and (not ceiling_ambient):
            return nil
```

Regression guard: `adversarial_escalation_attenuation_spec.spl` ->
"REGRESSION GUARD: an ambient-full ceiling under a narrow parent is REJECTED".
Legit full-under-full and concrete-narrowing cases still ACCEPTED (verified).
`capability_ambient_ceiling_fix.diff` holds the full working-tree diff (also
contains an unrelated parallel S5 Container/EscrowCap change — apply ONLY the
create_child_session hunk above if relanding after a WC sweep).

## LATENT issue to hand to the S-core sibling lane
The true root is `capset_subset` in `src/os/kernel/types/session_types.spl`
(sibling-owned): it treats an ambient-full `sub` as the empty set. It is
currently used ONLY by create_child_session, so my in-lane guard fully closes the
reachable hole, but the shared helper should also be hardened
(`full ⊆ sup` iff `sup` is full).

## Invariants now guarded (fail-closed)
1. Escalation: child cannot gain a cap the parent lacks (rejected>0, cap absent);
   fork of empty stays empty; ambient full() authorizes nothing via
   spawn_with_cspace; subrole cannot widen/regain rights; create_child_session
   ambient-ceiling bypass CLOSED.
2. Attenuation: wider path-prefix / broader device class / larger DMA / out-of-window
   extent / r->rw rights widening all denied by capability_kind_allows + dropped by mint.
3. Revocation: 3-level revoke_transitive cascade (no use-after-revoke); middle-token
   revoke spares ancestor; session-teardown epoch staleness denies bound caps;
   revocation idempotent (no resurrection).
4. Sealed/no-ambient: sealed session denies un-granted caps; unsealed denies ALL;
   resolve_tool nil + un-enumerable for absent caps; ambient hole unreachable from
   spawn_with_cspace/fork/spawn_llm (always pledged).
5. Token confusion: wrong-kind (FileRead vs IpcConnect, spawn vs kill) denied;
   port/object/generation mismatch denied.

## Test idioms learned (for reland)
- `gen` is a RESERVED keyword — never a param name (use `generation`).
- Optional nil idiom: assert nil with `expect(x == nil).to_equal(true)`; assert
  non-nil with `expect(x != nil).to_equal(true)`. `!= nil` on a nil value is
  UNRELIABLE in the interpreter — do not use `.to_equal(false)` on it.
- Enum constructors take plain int literals for u8/u16/u32/u64 fields.
