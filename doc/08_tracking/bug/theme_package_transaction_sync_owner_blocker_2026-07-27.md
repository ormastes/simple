# Theme package transaction synchronization-owner blocker

**Status:** open prerequisite  
**Candidate:** `4f84131c55` rejected and unintegrated  
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
- there is no canonical immutable wire codec for the resolved package/render
  snapshot. `ResolvedThemePackage` and `ThemeRenderSnapshot` retain
  object/array/map reachability and therefore cannot be the mutex payload or
  public transaction candidate;
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
Before another transaction implementation is opened:

1. define a persistent hosted theme session/store handoff created at process
   entry before worker dispatch and passed to every runtime refresh consumer;
2. define and test a canonical scalar theme-package/snapshot wire codec whose
   decoder reconstructs private render objects only after copying the wire
   under the store lock;
3. provide scalar/wire transaction reads for WM, GUI, and Web, and remove
   aggregate-return transaction APIs;
4. make source capture injectable so a counting/changing reader test proves
   one read of each canonical path;
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
transaction shape. Resume only after the persistent session handoff, immutable
wire codec, and scalar consumer surface are independently implemented and
reviewed.
