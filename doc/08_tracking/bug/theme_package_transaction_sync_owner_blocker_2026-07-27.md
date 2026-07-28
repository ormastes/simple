# Theme package transaction synchronization-owner blocker

**Status:** open prerequisite — re-verified against `origin/main` 2026-07-27,
still live (`ThemePackageTransactionStore` does not exist anywhere in `src/**`)  
**Candidate:** `4f84131c55` rejected and unintegrated, and **unrecoverable** —
never pushed, no longer resolves in the git or jj object store. The wire codec
`b1d0b3e27ff8` cited below **is** confirmed landed (ancestor of `origin/main`).
See [report](../../09_report/theme_hard_stops_unlanded_2026-07-27.md).  
**Iteration state:** cycle 2 stopped read-only; cycle 3 stopped and fully
reverted without a commit

## Finding

The first transaction candidate added prepare/commit/revision behavior, but
independent review rejected it because prepare reread mutable files, candidates
exposed mutable maps, commit performed an unlocked expected-revision check plus
sequential global writes, legacy loading returned uncommitted candidates, and
overflow coverage did not exercise real commit state.

Cycle 2 established that the owned single-read and immutable-wire repairs are
viable, but atomic publication is not honest within the current module:

- lazy module-global `Mutex?` initialization races and can create different
  locks for the first concurrent callers;
- eager module-global mutex construction is documented unsafe/corrupt in
  seed/freestanding/native entry-closure paths;
- current atomic integer APIs are single-threaded stubs, not CAS/Once;
- unlocked aggregate swaps or revision optimism cannot prove old-or-new reader
  visibility.

No repair edits or second commit were made. No runtime, bootstrap, or seed was
used.

## Cycle 3 result

Cycle 3 tested the proposed explicit-store boundary in an isolated worktree.
It was stopped before commit and every source edit was reverted after
high-capability review found that the current host/package interfaces still
cannot satisfy the contract:

- `install_default_host_wm_theme` returns only a snapshot. It does not hand a
  persistent transaction store/session to later refresh consumers.
- the hosted renderer worker branch dispatches before the current theme
  bootstrap, so constructing a store inside the installer is too late for a
  process-wide ownership guarantee;
- at that time there was no canonical immutable wire codec for the resolved
  package/render snapshot. `ResolvedThemePackage` and `ThemeRenderSnapshot`
  retain object/array/map reachability and therefore cannot themselves be the
  mutex payload or public transaction candidate;
- current consumer APIs either use legacy module caches or return aggregate
  objects. Existing fingerprint/color helpers and `ThemeChangedV1` are useful
  scalar/notification primitives, but there is no scalar-only transaction
  store/read surface shared by WM, GUI, and Web.

The discarded attempt would have stored mutable dictionaries and package
objects inside the published aggregate, returned aggregate aliases after
unlock, and created a fresh local store per install. Those shapes do not prove
atomic old-or-new visibility and were not committed.

## Required architecture before a fresh implementation lane

Hosted single-threaded bootstrap must create one
`ThemePackageTransactionStore` and inject it before concurrent readers start.
The store owns its real hosted mutex and one wire-backed published aggregate.
The canonical `theme-package-install-wire-v1` text codec has since landed at
`b1d0b3e27ff8e9c751ee8cbb7ec8f5e41bd4aaeb`. Its aggregate native ABI remains
unverified, so transaction candidates/publication must stay canonical text.
Before another transaction implementation is opened:

1. define a persistent hosted theme session/store handoff created at process
   entry before worker dispatch and passed to every runtime refresh consumer;
2. admit the landed codec's incremental native encoder/decoder ABI probe before
   using decoded aggregates across module boundaries;
3. provide scalar/wire transaction reads for WM, GUI, and Web, and remove
   aggregate-return transaction APIs;
4. resolve the source-capture design hard stop: add a cache-owning production
   wrapper that constructs the reader only on misses, and select strict versus
   legacy missing-core validation semantics;
5. reuse `ThemeChangedV1` only after a successful commit; it is the
   post-commit notification wire, not the package publication store.

Only after those interfaces land may a fresh session implement:

1. capture the registry and every referenced source exactly once into an owned
   source bundle;
2. validate, resolve, and hash only those captured bytes;
3. expose a scalar/canonical wire candidate with no reachable mutable maps;
4. stage the complete next aggregate outside the lock;
5. acquire the injected store lock, recheck expected revision, and swap one
   coherent state;
6. treat identical identity/content as a no-op, fail overflow/stale/invalid
   before writes, and never return an uncommitted candidate;
7. test real max-revision rollback and deterministic competing commits against
   an isolated store.

The three-cycle cap is exhausted for this session. Do not retry the same
transaction shape. Resume only after the persistent session handoff,
source-capture hard stop, native codec ABI evidence, and scalar consumer
surface are independently implemented and reviewed. See
[source-capture hard stop](theme_package_source_capture_design_hard_stop_2026-07-27.md).
