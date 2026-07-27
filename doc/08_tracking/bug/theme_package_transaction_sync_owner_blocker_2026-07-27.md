# Theme package transaction synchronization-owner blocker

**Status:** open prerequisite  
**Candidate:** `4f84131c55` rejected and unintegrated  
**Iteration state:** cycle 2 stopped read-only; cycle 3 intentionally unused

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

## Required owner before cycle 3

Hosted single-threaded bootstrap must create one
`ThemePackageTransactionStore` and inject it before concurrent readers start.
The store owns its real hosted mutex and one wire-backed published aggregate.
Only then may a fresh implementation:

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

Do not begin cycle 3 until that bootstrap owner/injection boundary is available.
