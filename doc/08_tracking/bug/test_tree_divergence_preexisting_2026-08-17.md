# Pre-existing test-tree divergence, and the mirror the ed25519 fix missed

**Status:** OPEN (backlog pre-existing); the newly-introduced pair is FIXED here.

## The regression this fixes

The ed25519 secret-scalar-branch fix updated
`test/01_unit/lib/crypto/ed25519_ct_property_spec.spl` but left its live
duplicate `test/unit/lib/crypto/ed25519_ct_property_spec.spl` untouched.
That pair was byte-identical before the fix landed, so the change newly
diverged it. Detected by:

```
check-test-tree-divergence-delta: FAIL — 1 newly introduced:
  unit:lib/crypto/ed25519_ct_property_spec.spl
```

Mirrored rather than baselined: the divergence was introduced by that change,
so the scoped-delta escape hatch explicitly does not cover it.

## The pre-existing backlog (recorded, not adopted)

`.claude/rules/vcs.md` requires that landing on a divergence delta-PASS record
the pre-existing offender list. Guard 7 in `--ref` mode is RED identically at
the base and at the fixed tip:

```
check-test-tree-divergence: FAIL — 829 diverged vs 813 baselined
  (17 new, 1 fixed-but-still-baselined); 3 mirror-only
  (1 unallowlisted, 0 stale-allowlist)
check-test-tree-divergence-delta: PASS — 19 pre-existing offender(s),
  0 introduced by this range
```

The full 829-entry list captured at the base is stored alongside this file as
`test_tree_divergence_preexisting_2026-08-17.txt`. This backlog is owned by
whichever lane last touched the duplicate trees; nothing here widens it.
