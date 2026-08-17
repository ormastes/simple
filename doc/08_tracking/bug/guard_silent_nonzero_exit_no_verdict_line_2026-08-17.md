# A guard that exits nonzero with ZERO output is indistinguishable from a real FAIL — and it cost a real authorisation

- **Filed:** 2026-08-17
- **Severity:** P1 — not because the guard was wrong, but because its silence was
  read as a content failure and used as the premise for a human decision
- **Status:** FIX EXISTS, UNPUSHED (local `1e9058670c6`); origin/main still silent

## The defect

`scripts/check/check-native-trailing-default-param.shs` at `origin/main`:

```sh
39: set -eu
54: test -x "$SIMPLE_BINARY"      # SIMPLE_BINARY defaults to bin/simple
```

A bare `test -x` under `set -eu` **terminates the script**. `bin/simple` is a
gitignored symlink, absent in a fresh `git worktree`, so the guard dies at line
54 having printed nothing at all.

## Reproduced 2026-08-17 (both versions, same host)

```
$ SIMPLE_BINARY=/nonexistent sh /tmp/ntdp_origin.shs   # origin/main version
rc=1   bytes=0                                          # <-- SILENT

$ SIMPLE_BINARY=/nonexistent sh scripts/check/check-native-trailing-default-param.shs
rc=2   bytes=244
ERROR — nothing was checked: no executable compiler at '/nonexistent'
```

## Why this is worse than an ordinary bug

The repo's verdict convention exists precisely so a caller can tell the three
states apart. A silent `exit 1` collapses two of them:

| what happened | what a caller sees |
|---|---|
| the fixture genuinely failed to compile | exit 1 |
| no compiler was present; nothing ran | exit 1 |

**Measured consequence:** a coordinating lane obtained a *user authorisation to
bypass* on the stated premise that this guard was blocking a push. It never
fired — it had exited before checking anything. A guard's silence became the
evidence for a decision that only a human was allowed to make. Absence of
evidence was consumed as evidence.

### The inference to retract, stated plainly

The same silent run also produced the conclusion **"origin is NOT red on this
guard"**, which was relayed onward as fact to at least one other lane. That
conclusion is unsupported by the run that produced it, and the general rule is
worth stating in one line because it is the entire reason the verdict convention
exists:

> **A guard that checked nothing cannot certify green any more than it can
> certify red.** A silent `exit 1` is not evidence of failure, and it is not
> evidence of success either. It is the absence of a measurement, and the only
> honest reading of it is `ERROR — nothing was checked`.

Both directions of the mistake were made from the same 0-byte output within one
session: first "this guard is blocking my push" (it was not running), then "origin
is clean on this guard" (nothing had been measured). **Anyone who received the
"origin is not red" claim should treat it as withdrawn.**

And in this case the reassuring half was also substantively wrong. Where
`bin/simple` is present the guard *does* run, and it FAILs on real content:
`MIR lowering error: unresolved method call: bump` — a general multi-module
`native-build` defect filed as
`doc/08_tracking/bug/native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md`.
So the bypass premise was wrong twice over: the guard did not fire for that lane,
**and** the content it gates is genuinely broken.
fired — it had exited before checking anything, and `origin` is not red on it.
A guard's silence became the evidence for a decision that only a human was
allowed to make. Absence of evidence was consumed as evidence.

This is the same family as
`doc/08_tracking/bug/guards_hardcode_stale_seed_binary_census_2026-08-17.md`
(27 files hardcode `$ROOT/bin/simple`, non-injectable). Both defects come from
treating the compiler binary as an ambient given rather than an injected,
checked input: that row is "the guard measured the WRONG binary", this row is
"the guard measured NO binary and said nothing".

## The fix

Already implemented in unpushed local commit `1e9058670c6` ("fix(guards): give
the trailing-default-param guard a verdict contract; census the vacuous
guards", +204/-6): the missing-binary path now emits
`ERROR — nothing was checked: no executable compiler at '<path>'` and exits 2,
with `SIMPLE_BINARY` injectable. Verified above. **It is not on origin** — it
needs to land.

## Generalisation worth acting on

Any guard combining `set -e`/`set -eu` with a bare `test`/`[` prerequisite check
has this defect. The prerequisite must be written as an explicit branch that
emits `ERROR — nothing was checked: ...` and exits 2. A sweep for
`set -eu` + bare `test -x` across `scripts/check/**` is the obvious follow-up and
is NOT yet done.

## Not a defect, but it wastes lanes

Three lanes have now diagnosed a "33-minute push hang" or "51-minute push hang"
as a network problem. It is not: the pre-push hook runs a chain of ~61 guards
that legitimately takes on the order of an hour, and emits no progress output
while doing so. Worth a progress line per guard.
