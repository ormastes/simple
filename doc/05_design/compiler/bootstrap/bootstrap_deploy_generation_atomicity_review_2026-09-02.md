<!-- codex-design -->
# Bootstrap Deployment Generation Atomicity — Design Review (2026-09-02)

## Determination

**STATUS: DESIGN BLOCKED / IMPLEMENTATION FAIL**

The proposed immutable generation-directory plus single pointer switch is the
right publication model, but it is safe only if the pointer is the sole runtime
authority and the generation is closed, self-verifying, and durable before the
switch. The current per-file model cannot satisfy atomic visibility. In this
worktree, `bootstrap-deploy-transaction.shs` is absent even though bootstrap and
rollback source it; therefore its current implementation could not be reviewed
directly. This review uses its surviving callers and the independent audit and
does not credit an unavailable implementation.

## Canonical layout and state machine

For each canonical platform directory `P`:

```
P/generations/<generation-id>/
  manifest.env
  deploy-receipt.env
  authority/...
  bin/{simple,simple_seed,simple_ui_backend,simple_mcp_server,simple_lsp_mcp_server,...}
P/CURRENT -> generations/<generation-id>
P/PREVIOUS -> generations/<prior-generation-id>       # advisory history only
```

States are `constructing -> admitted -> current -> retired`; generation
contents never change after `admitted`. A generation ID is a digest of the
canonical manifest (or contains that digest), not a PID/time name. Temporary
construction directories and pointer names are never launcher-visible.

## Required invariants

1. **Closed generation.** `manifest.env` declares an exact, unique artifact set,
   including absence. Every declared regular file has type, relative path,
   mode, size, SHA-256, and role. Unknown files, missing files, symlinks,
   hard-linked mutable aliases, duplicate keys/paths, and writable admitted
   files are rejected. The set includes compiler, seed policy, UI, MCP/LSP,
   digest sidecars, immutable launcher templates/policy, Stage 3/4 provenance,
   planner/continuation authority, and receipt.
2. **Authority closure.** Receipts contain only generation-relative authority
   paths and bind platform, source fingerprint, exact manifest digest, parent
   generation/digest, policy, creation transaction, and every retained
   authority digest. Admission invokes the canonical Stage 4 verifier, which
   transitively verifies Stage 3, under the publication lock immediately before
   switching. Build-tree paths are diagnostic only and grant no later authority.
3. **One publication mutation.** No artifact is copied, deleted, or rewritten
   in the selected generation. Publication is exactly one atomic replacement of
   `P/CURRENT` after complete admission and durability. A reader opening before
   or after that replacement resolves wholly to the old or new immutable
   generation; it can never observe a mixed set.
4. **Exact companions / stale rejection.** Full-tooling publication requires
   the full policy-defined set. Resume or `--no-mcp` may construct a quarantined
   generation but cannot select it as canonical full tooling. Omission means
   manifest-declared absence; launchers fail closed and never search a prior
   generation, legacy flat path, build tree, environment fallback, or Rust seed.
5. **Launcher authority.** Stable `bin/simple*` entrypoints are immutable,
   generation-resolving launchers (or stable links to such launchers). On every
   invocation each launcher resolves `CURRENT` once to one canonical generation,
   validates the role and manifest/receipt binding, and executes only the
   generation-relative target. MCP/LSP digest checks use sidecars from that same
   resolved directory. Environment overrides are explicitly non-production and
   cannot produce acceptance receipts.
6. **Resume semantics.** Resume may reuse only a content-addressed `admitted`
   generation whose manifest, authority closure, intended platform/policy, and
   parent-current CAS value all reverify. A `constructing` generation is never
   resumed as authority: it is deleted/quarantined and reconstructed. If its
   expected parent no longer equals `CURRENT`, resume refuses rather than
   rebasing or silently publishing.
7. **Receipts.** The deploy receipt is inside and hashed by the generation
   manifest through a non-cyclic scheme (for example, manifest hashes a receipt
   body whose generation identity is computed from the artifact/authority
   section). A separate append-only operation receipt records expected old and
   selected new generation digests, lock identity, result, and recovery action;
   it is evidence, never the selection authority. No `CURRENT` switch precedes
   the immutable deploy receipt.
8. **Rollback authority.** Rollback is a new CAS-protected pointer selection,
   not file restoration and not trust in `PREVIOUS`. The requested target must
   be an existing admitted generation whose full manifest and canonical
   Stage 4->Stage 3 authority reverify. The operator supplies/acknowledges the
   exact target digest; policy controls downgrade. A rollback receipt binds
   expected current, target, reason, and both authority digests. Only `CURRENT`
   selects runtime state.
9. **Crash recovery.** Before switch, crashes leave an unselected directory;
   recovery verifies then quarantines/removes it. After a successful switch,
   the new generation is current even if operation-receipt/history maintenance
   was interrupted. Startup derives truth solely from `CURRENT`, verifies it,
   and repairs advisory `PREVIOUS`/operation bookkeeping without switching.
   Invalid/missing/dangling `CURRENT` fails closed; recovery never guesses the
   newest directory.
10. **Concurrency.** One same-filesystem writer lock covers construction-name
    reservation, final admission, expected-current comparison, and switch.
    Pointer replacement is CAS: observed `CURRENT` must equal the transaction's
    recorded parent. Locks do not protect readers; immutability plus atomic
    pointer resolution does. Garbage collection takes the writer lock and may
    delete only generations not referenced by `CURRENT`, `PREVIOUS`, active
    leases, or retained operation receipts. Readers that need multiple opens
    retain the resolved generation path/lease for the entire operation.

## macOS / POSIX portability constraints

- Generation directory and `CURRENT` temporary entry must be on the same
  mounted filesystem as `P`; cross-device rename is forbidden. The final switch
  must use one `rename(2)`-equivalent replacement of a temporary relative
  symlink/directory entry. Shell `ln -sfn`, unlink-then-link, and multi-command
  `mv` recipes are not accepted as proof; use the repository's audited portable
  helper or a tiny helper that exposes rename without a visibility gap.
- POSIX rename atomicity is namespace atomicity, not power-loss durability.
  Before switch, fsync every generated regular file and required directory;
  after switch, fsync `P`. On macOS/APFS, use `fsync` and, where the durability
  contract requires stable storage rather than kernel-cache persistence,
  `F_FULLFSYNC`; unsupported durability must fail admission or be explicitly
  classified non-durable. Pure POSIX shell has no portable fsync primitive.
- Require `/bin/sh` syntax. Do not depend solely on GNU `readlink -f`,
  `realpath -m`, `stat -c`, `sha256sum`, `flock`, `renameat2`, or GNU `mv -T`.
  Canonicalization must use existing portable helpers and require exact input
  spelling, no symlinked ancestors, and confinement under canonical `P`.
  Hashing must support the established `shasum -a 256` macOS path (or an audited
  repository helper). Modes require both BSD and GNU `stat` handling.
- Relative pointer targets are mandatory and must contain only admitted safe
  components. Do not infer safety from `readlink` text alone: canonicalize the
  resolved directory, require it beneath `P/generations`, and reject nested or
  absolute links. Case-folding/case-preserving filesystems require collision
  checks on normalized generation and artifact names.
- Atomic replacement must preserve a valid old `CURRENT` on every pre-switch
  error. Signal traps may clean temporary names but are not correctness or
  crash-recovery mechanisms. Directory permissions/umask must prevent another
  user from modifying construction or admitted generations.

## Findings against current callers

- **Critical:** publication is described and called as per-file transaction
  application, so readers can observe mixed generations; rollback repeats that
  model.
- **Critical:** canonical resume uses `--no-mcp`, omits the seed transaction,
  and conditionally omits MCP/LSP; flat destinations therefore retain stale
  companions unless publication is changed to exact closed generations.
- **High:** `setup.shs` rewrites launchers after artifact mutation and its MCP/LSP
  wrappers search flat release paths. Launcher success is not part of one atomic
  publication, and fallback search is incompatible with generation integrity.
- **High:** deploy receipts are written after artifact application; rollback
  validates hashes but does not visibly invoke canonical Stage 4/Stage 3
  semantic verification before mutation.
- **Critical/current-tree integrity:** both deploy and rollback source the
  missing `scripts/bootstrap/bootstrap-deploy-transaction.shs`; no deployment
  or rollback should be considered available until that dependency exists and
  conforms to this contract.

## Acceptance gate for implementation review

Static review must trace every production launcher and receipt consumer through
one resolved generation. Later verification must inject interruption before and
after every durability/switch boundary, concurrent writers with identical and
different parents, stale/incomplete companions, tampered authority, dangling
and aliased pointers, resume after parent change, rollback downgrade, and a
reader holding the old generation across a switch. At every observation the
allowed result is old-complete, new-complete, or fail-closed—never mixed.
