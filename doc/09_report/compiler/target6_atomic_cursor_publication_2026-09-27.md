# Target 6 atomic inventory/cursor publication (2026-09-27)

The compiler inventory bridge previously published
`source-inventory/CURRENT` and then wrote `compile-events/CURRENT`. If the
second write failed, the next refresh found an inventory/cursor binding
mismatch and could not replay from the old cursor.

The isolated source now computes the Git head, consumed filesystem row count,
and journal prefix digest before publication. The inventory publisher writes
the immutable generation file, then atomically replaces one `CURRENT` record
containing both its digest and the event cursor under the existing publication
lock. A failed pointer rename leaves the prior digest and cursor together.
Unchanged inventory generations may still advance their cursor through the
same atomic replacement. A bare-digest `CURRENT` reads the old separate cursor
for migration; a combined record never falls back to that legacy cursor.

The bridge now captures `CURRENT` once to validate the cursor against the
matching immutable inventory generation. Before replacing that record, the
publisher compares its full-content SHA-256 under the publication lock. A
writer whose observation is stale returns `publish-cursor-superseded`; it
cannot overwrite a newer cursor merely because the inventory generation has
the same content digest. A post-publish read that lands on a different
generation returns `inventory-publication-raced` instead of reporting a
successful refresh for a different writer's result.

Focused SPipe unit coverage rejects malformed cursor metadata before
publication and rejects a stale writer without changing `CURRENT`. The Unicode
untracked integration spec checks a combined pointer
and a warm refresh despite a corrupt legacy cursor. The existing overflow
spec ensures rejected filesystem events do not publish Git changes. These
tests still need an admitted current-source pure-Simple runner: the only
locally available `bin/release/.../simple` announces itself as a Rust bootstrap
seed, and the historical admitted pure-Simple Stage2 native probe timed out
after 120 seconds without producing an executable. Neither is Target 6
acceptance evidence. Concurrent-writer, crash/rename-failure, replay, and
native performance cohorts remain open.

## Historical Stage2 native diagnostic

Adding `--entry-closure` to the focused native-build command reduced its
source set to 28 modules and produced a 135 KB executable in 3.8 seconds.
The final diagnostic rebuild took 3.7 seconds (1 compiled, 27 cached;
SHA-256
`8dd77a6d5a0eb36b81487ea850806cbeff5c3dcc9c85fd54cb82d1476dafa1fa`).
The probe remains under `build/mini_builds/target6_atomic_cursor_probe/`.
The first run used a cache path outside the inventory owner's allowed
`build/scv` suffix; the corrected run reached inventory publication but
returned `publish-encode-empty`. A third and final diagnostic showed why:
the historical Stage2 native Option unwrap of the valid cold-initialization
result yielded generation `-1037955087042871295` and zero entries, so the
canonical encoder correctly refused it. The isolated source now binds that
`Some(seed)` through a pattern match, avoiding the observed unwrap path.
The three-cycle limit stops further testing of this probe in this session.
This does not prove current-source behavior or Target 6 acceptance.
