# Cold HIR read checkout inventory from the machine cache

The entrypoint publishes compile inventory and immutable snapshots under the
checkout's `build/scv`. Cold HIR instead called
`compile_source_inventory_read_current_v1(machine_cache_root())`. The normal
machine root is host-shared and project-namespaced, so it fails the inventory
validator's `build/scv` / `.simple/scv` ownership contract. The resulting error
is `cold HIR inventory admission failed: inventory-cache-root-invalid`.

Reproducer evidence: the explicitly renewed positive and negative projections
under `/mnt/simple-bootstrap-6b2/native-cache-parent-routing-20260930/` passed
Git inventory admission and parsed/lowered one module, then failed at that
read. The compiler was
`203e210012adcfb21d29571506bfa9e39cb56eb1aabbd89a68c8efd20212533b`.
These were isolated tests, not changes to a live bootstrap producer or cache.

The fix introduces pure shared SCV root resolution. Publication uses the
checkout root; snapshot-open and cold HIR derive the inventory root from the
exact snapshot path and revision, constrained to that checkout's `build/scv`
or `.simple/scv`. Cold HIR gets the current checkout and admission environment
through SOSIX. Existing snapshot containment, receipt, generation and digest
checks remain mandatory. Missing/malformed/foreign snapshot routing fails
closed. No tree scan or mutable admission cache is added.

`machine_cache_root()` and exact `SIMPLE_CACHE` behavior are unchanged for
machine-tier caches and package indexes. An operator override cannot relocate
an already admitted checkout-owned snapshot. This corrects the reader's use
of the wrong cache domain instead of requiring callers to set `SIMPLE_CACHE`
to a checkout directory.

Prevention covers the default machine-cache mismatch, arbitrary explicit
machine roots, both owned SCV layouts, Windows path spelling, POSIX backslash
preservation, foreign roots, traversal, malformed revisions and revision
mismatch. Small native source projections qualify the production resolver
bodies; full rebuilt compiler/bootstrap qualification remains separate.

## Digest domains discovered behind the root gate

With a compatible private `SIMPLE_CACHE`, the retained producers read valid
inventory but report `cold HIR inventory admission failed: ok`. The reason is
not corruption: the entrypoint exports the hash of snapshot manifest rows
(`path|sha256_content|size`), whereas cold HIR and typed-receipt construction
compare the hash of canonical `CompileSourceInventoryV1` encoding (schema,
generation, semantic fields). Those hashes intentionally differ.

`CompileSourceInventoryBindingV1` now names both domains. The existing
`SIMPLE_SCV_INVENTORY_DIGEST` remains the snapshot-manifest digest for package
indexes and snapshot consumers. New `SIMPLE_SCV_SOURCE_INVENTORY_DIGEST`
carries the canonical digest from inventory refresh to cold HIR and its typed
receipt constructor; it also participates in native environment identity.
Publication rechecks bounded CURRENT metadata after snapshot acquisition and
rejects a changed canonical generation. Neither source scanning nor digest
validation is bypassed. Digest failures now identify the canonical mismatch
instead of printing a successful read reason. Missing new canonical authority
fails closed; old externally prepared environments must be readmitted by the
updated entrypoint.

The snapshot manifest is still authenticated by the existing snapshot-open
provenance, inventory hash, frozen-content and receipt validation; the new
binding helper's 64-hex shape check does not replace that authority. The
post-snapshot CURRENT check relies on the event publisher's monotonic encoded
generation and compare-and-publish contract: a changed generation cannot
return to the same digest through an ordinary source edit/revert. Deliberate
out-of-protocol pointer rollback (ABA) is outside that assumption. The typed
receipt owner additionally checks every lowered source against the admitted
canonical inventory. No additional tree scan is introduced.

Regression source covers a canonical generation changing after refresh but
before publication, requiring `source-inventory-digest-mismatch`, and verifies
the reread precedes environment publication. This case was added after the
third native attempt and remains unexecuted with the rest of the native bodies.

The entrypoint uses canonical current directory as its checkout root, not a
Git root search. HIR uses SOSIX cwd and the same path normalization. A parent
checkout snapshot cannot be inherited from a child cwd. Windows drive and
verbatim UNC spellings normalize consistently; POSIX backslashes are retained.

## Qualification: WARN / native TEST_BLOCKED

All three bounded fixture attempts are preserved beneath
`/mnt/simple-bootstrap-6b2/compiler-inventory-root-20260930/`:

1. `attempt1`: harness preflight could not read the Windows worktree Git blob
   using Linux Git. The baseline now comes from Windows Git explicitly.
2. `attempt2`: producer `203e2100` parsed/lowered one module, then hit the
   baked-in digest-domain failure above before code generation.
3. `attempt3`: retained pure producer `9088595d` and its matching frozen
   runtime also parsed/lowered one module with zero any-escape/enum diagnostics,
   then hit the same digest-domain failure before native test bodies.

The source projection includes real production resolver and digest-binding
functions, correct-domain acceptance, swapped-domain rejection, malformed
authority rejection, and separate default/explicit machine-cache environments.
Its `plan.json` records exact source, projection and producer hashes. **Zero
native assertions executed.** No general selfhost test runtime or rebuilt
compiler qualification is claimed. The attempt cap is reached; continuation
requires a producer rebuilt with this admission fix. No live producer or cache
was altered, no blanket cleanup or validation bypass was performed.
