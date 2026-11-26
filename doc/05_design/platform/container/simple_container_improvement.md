# Simple Container Improvement — detail design

**Date:** 2026-11-25
**Architecture:** `doc/04_architecture/platform/container/simple_container_improvement.md` (authoritative decisions, phases, and evidence policy)
**Base:** `release/1.0.0` at `64dfa6d980f`
**Status:** Increment 1 detail design (architecture Phases 0–1). Later phases are planned there and are not implemented by this increment.

## 2026-11-25 Increment 1 scope

Implements the architecture's immediate target — *SCV-compatible shared immutable storage with selectable hashing* — plus the versioned container contracts that later phases build on:

1. Hash policy dispatch: XXH3-128 (default), GxHash-128 (pinned profile), BLAKE3-256 (optional), legacy SHA-256. Fail-closed on unknown selection; never emit one algorithm's bytes under another tag.
2. Versioned `ObjectRecordV1` with digest aliases, decoupling lookup keys from authoritative object identity.
3. A collision-safe immutable object store (ingest → staged verified no-replace publication → read-only open) reusing the SCV publication discipline, with pins, root publication, and dry-run-first GC to quarantine.
4. Container capability report contract (architecture §4.2) with fail-closed admission.
5. Container lifecycle journal contract (architecture §11.4) with idempotent recovery-action planning.

Explicitly out of scope for this increment: native provider wiring (Linux/Windows/FreeBSD/macOS), SimpleOS pager/PMM changes, VFS enforcement, live memory-limit updates, SCV internal rewiring. The store accepts `sha256_<hex>` legacy aliases so container manifests can reference existing SCV objects without touching SCV internals.

## Interfaces and storage

### `src/lib/common/hash/hash_policy_v1.spl` (new)

```
pub const HASH_POLICY_V1_XXH3_128 = "xxh3-128"
pub const HASH_POLICY_V1_GXHASH_128 = "gxhash-128"
pub const HASH_POLICY_V1_BLAKE3_256 = "blake3-256"
pub const HASH_POLICY_V1_SHA256_LEGACY = "sha256"
pub const HASH_POLICY_V1_GXHASH_PROFILE = "gxhash-4.0.0-scalar"

pub struct HashDigestV1:
    policy: text        # echoed policy tag actually used
    profile: text       # algorithm profile (e.g. gxhash pin), "" when not applicable
    status: text        # "ok" | "unsupported"
    reason: text        # fail-closed reason, "" on ok
    hex: text           # lowercase digest hex; "" unless ok
    byte_len: i64       # digest width in bytes; 0 unless ok

pub fn hash_policy_v1_default() -> text                      # "xxh3-128"
pub fn hash_policy_v1_supported(policy: text) -> bool
pub fn hash_policy_v1_digest(policy: text, bytes: [u8]) -> HashDigestV1
```

Backends: `std.common.hash.xxh3.{xxh3_128_hex}` (16 B), `std.common.hash.gxhash.gxhash128` (16 B, little-endian bytes → hex), `std.common.crypto.blake3.blake3_hex` (32 B), `std.common.crypto.sha256` hex (32 B). GxHash is the in-tree pure-Simple scalar port (software sbox; no AES hardware requirement); its pinned profile string is recorded in every digest and alias. Unknown policy → `status: "unsupported"` with a precise reason; a known policy never falls back to a different algorithm.

### `src/lib/common/storage/object_record_v1.spl` (new)

```
pub const OBJECT_RECORD_V1_VERSION = 1

pub struct DigestAliasV1:
    algorithm: text          # policy tag, e.g. "xxh3-128"
    algorithm_profile: text  # pinned profile or ""
    digest_hex: text

pub struct ObjectRecordV1:
    format_version: i64
    object_key: text         # authoritative immutable key, e.g. "xxh3-128_<hex>" or legacy "sha256_<hex>"
    logical_length: i64
    generation: i64
    aliases: [DigestAliasV1]

pub fn object_record_v1_encode(record: ObjectRecordV1) -> text            # SDN, canonical field order
pub fn object_record_v1_decode(text: text) -> ObjectRecordV1              # invalid input -> format_version 0
pub fn object_record_v1_valid(record: ObjectRecordV1) -> bool
```

SDN by default (repo rule). Decode is strict: unknown version, missing fields, or malformed aliases yield `format_version: 0` (invalid), never a partially trusted record.

### `src/lib/nogc_sync_mut/storage/immutable_store_v1.spl` (new)

Store root layout (all paths relative to a caller-provided root):

```
objects/<key[0:2]>/<key>.obj      # immutable payload, no-replace publication
records/<key>.sdn                 # ObjectRecordV1
aliases/<algorithm>/<digest_hex>  # file content = object_key text, no-replace
roots/<name>.sdn                  # root pointer: a CACHE of the head generation (may lag)
roots/<name>.g<N>.claim           # generation N>=2, no-replace, never deleted: the CAS commit
pins/<pin_id>/owner              # append-only pin dir: raw owner text
pins/<pin_id>/refs/<key>         # file content is the key text, one per retained object
collisions/<algorithm>/<digest_hex>_<n>.sdn   # collision records
staging/<unique>                  # private staging, removed on success/failure
quarantine/<date>/                # GC moves, never unlinks
```

```
pub struct StoreIngestV1:
    status: text        # "ok" | "rejected"
    reason: text
    object_key: text
    alias_hex: text
    reused: bool        # true when an existing verified object satisfied the ingest

pub struct StoreOpenV1:
    status: text        # "ok" | "missing" | "corrupt"
    reason: text
    bytes: [u8]

pub struct StoreGcV1:
    status: text
    reason: text
    dry_run: bool
    unreachable: [text]   # object keys
    moved: i64

pub fn immutable_store_v1_init(root: text) -> text                     # "" ok, else reason
pub fn immutable_store_v1_ingest(root: text, bytes: [u8], policy: text) -> StoreIngestV1
pub fn immutable_store_v1_open(root: text, object_key: text) -> StoreOpenV1
pub fn immutable_store_v1_publish_root(root: text, name: text, manifest: text, expected_generation: i64) -> text
pub fn immutable_store_v1_pin(root: text, pin_id: text, owner: text, refs: [text]) -> text
pub fn immutable_store_v1_release_pin(root: text, pin_id: text) -> text
pub fn immutable_store_v1_collect(root: text, dry_run: bool) -> StoreGcV1
```

**Ingest pipeline** (collision-safe, architecture §8.4):

1. `hash_policy_v1_digest(policy, bytes)`; unsupported → rejected.
2. Candidate lookup at `aliases/<algorithm>/<digest_hex>`. On hit: read the record, open the object's bytes, **byte-compare**. Equal → return `reused: true` with the existing key. Different → collision: write a collision record, derive the next free disambiguated key `<algo>_<hex>_c<n>` (bounded scan, n ≤ 64, then explicit rejection), and publish under that key.
3. Miss → object key `<algo>_<hex>`; stage payload + record in `staging/`, verify read-back (length + recomputed digest), then `file_publish_noreplace_raw` into `objects/` and `aliases/`.
4. Concurrent winner: if no-replace publication loses, open and byte-verify the winner; identical bytes → reuse; different bytes → collision path (3-way safe).

**Roots:** manifest text lists object keys (one per line, SDN header with `generation`). Generation 1 is the pointer itself, created via no-replace. An update with `expected_generation = N` walks the claim chain `g<N+1>, g<N+2>, ...` from the cached pointer to find the head, refreshes the pointer, and fails `root-generation-mismatch` unless head == N; it then no-replace-publishes `roots/<name>.g<N+1>.claim`. That claim is the commit, so exactly one writer wins per generation. The pointer write that follows only refreshes a cache: a stalled writer that moves the pointer back loses nothing, because claims are never deleted and the next walk finds the head again. The walk is bounded (4096 steps).

**GC:** reachable set = union of object keys referenced by every root (pointer and claim-chain head; superseded claims are history) and every pin. GC fails closed: a missing or unlistable `roots/` or `pins/`, or any unreadable or corrupt doc, rejects the run with nothing collected. Default dry-run lists unreachable keys; `dry_run: false` moves them to `quarantine/<date>/` (SCV discipline — never unlink). Live kernel mappings and in-flight staging are represented by pins; a pin is never collected by GC.

### `src/lib/common/contracts/container/capability_report_v1.spl` (new)

Value-only contract mirroring `host_capability_v1.spl` style (Simple has no trait syntax; platform leaves own executors):

```
pub struct ContainerCapabilityReportV1:
    host_os: text
    host_arch: text
    guest_abi: text
    isolation_kind: text
    client_authority: text
    launch_qualified: bool
    filesystem_confinement: bool
    root_view_kind: text
    ephemeral_cleanup: bool
    durable_recovery: bool
    memory_accounting: text
    memory_hard_limit: bool
    memory_limit_update: bool
    memory_reclaim: bool
    readonly_file_backing_reuse: bool
    explicit_shared_memory: bool
    filesystem_save_load: bool
    process_checkpoint: bool
    provider_version: text
    evidence_revision: text

pub struct ContainerCapabilityRequirementV1:   # required_* mirror the report
    ...
pub fn container_capability_v1_admission_reason(report, requirement) -> text   # "" = admitted, fail-closed reasons
pub fn container_capability_report_v1_empty() -> ContainerCapabilityReportV1
```

Admission is fail-closed per architecture §4.2: a requirement for `memory_hard_limit` (or any capability) is admitted only when the report affirms it with a non-empty `evidence_revision`; unknown accounting kinds are rejected, never weakened.

### `src/lib/common/contracts/container/lifecycle_journal_v1.spl` (new)

```
pub const LIFECYCLE_PHASE_V1_{CREATED,STARTING,RUNNING,STOPPING,STOPPED,DESTROYED}
pub struct ContainerLifecycleJournalV1:
    format_version: i64
    container_id: text
    generation: i64
    provider_id: text
    phase: text
    owned_paths: [text]
    owned_objects: [text]
pub fn lifecycle_journal_v1_encode/decode(...)     # same strictness as object_record_v1
pub fn lifecycle_recovery_actions_v1(journal: ContainerLifecycleJournalV1, native_alive: bool) -> [text]
```

`lifecycle_recovery_actions_v1` is a pure decision function returning an ordered, idempotent action list (`stop-descendants`, `revoke-handles`, `detach-view`, `remove-owned-path`, `remove-owned-object`, `retain-saved-root`, `mark-destroyed`) derived from phase + native liveness, per architecture §11.3–11.4. Executors live in platform leaves.

## Pipeline

Lane A (hash policy) and lane C (contracts) are independent. Lane B (store) depends only on lane A's published signatures above; both compile against this document. Lane D (specs) runs after A–C merge into the lane branch.

## Failure behavior and cache

- Every public fn returns an outcome struct or reason text; no panics on hostile input. Decode failures produce invalid sentinels (`format_version: 0`), not partial values.
- Checked arithmetic on lengths/offsets; bounded collision scan; bounded alias/record reads (reuse `file_read_regular_no_follow_bounded_bytes` discipline from `std.scv.file_buffer`).
- No caching in increment 1 beyond the OS page cache; the store is correct under repeated open.

## Shared scenario helpers

Specs use real temp dirs (`build/` scratch via existing spec helpers), never mocks of the store itself. Forced-collision tests inject an alias file pointing at a different-bytes object to exercise the collision path deterministically (the hash backends themselves are not mockable).

## Status 2026-11-25

Increment 1 designed; implementation lanes A–D dispatched per `doc/03_plan/platform/container/simple_container_improvement.md`.

## Status 2026-11-26

Increment 1 implemented and verified: 6 specs / 60 examples green on the Windows host. `immutable_store_v1` moved to `src/lib/nogc_sync_mut/storage/` (it does file I/O; `common/` is pure). Docs moved under `doc/<phase>/platform/container/`. Spec mirror generated. Lands via PR to `release/1.0.0`.

## 2026-11-26 Increment 2 scope

Increment 1 landed (PR #11818). Increment 2 has three lanes. Lane 0 lands first, alone. It changes the store's API and on-disk format while the store still has no non-spec consumers.

### Lane 0 — store API/format hardening (`work/container-inc2-hardening-20261126`)

1. **Counted docs.** Root and pin docs carry a `count: <n>` header field equal to the number of key lines. Decode rejects a missing, non-canonical or mismatched count, so a document truncated at a line boundary can no longer decode as valid.
2. **Canonical integers.** Every decoded integer (`format_version`, `generation`, `count`, collision suffix `_c<n>`) must be canonical decimal: no leading `0` except `0` itself, no sign, no spaces. `_c01` and `generation: 007` are rejected.
3. **Pinned ingest.**
   ```
   pub fn immutable_store_v1_ingest_pinned(root: text, bytes: [u8], policy: text,
           pin_id: text, owner: text) -> StoreIngestV1
   ```
   The key is added to pin `pin_id` (creating it for `owner`) **before** the object becomes visible under that key. That covers the collision-disambiguated key too, so GC can never collect an ingested-but-unrooted object between ingest and root publication. The pin is an existing record, extended with the key appended only if absent. The plain `immutable_store_v1_ingest` remains for callers that pin explicitly.
4. **Pin owner check.** Updating an existing pin whose `owner` differs returns `pin-owner-mismatch`; it never replaces another owner's refs. `immutable_store_v1_release_pin` gains an `owner` parameter and enforces the same check.
5. **Aligned bounds.** The pin read bound equals the root read bound (4 MiB), and `_ISV1_MAX_REFS` is lowered to 16384. Any pin the API accepts must also fit under the read bound.
6. **GC name validation.** GC applies `_isv1_name_valid` to every root and pin file stem. A stem that fails validation rejects the run, failing closed.
7. **Domain units.** `ObjectRecordV1.format_version/logical_length/generation` and `HashDigestV1.byte_len`, plus the bool returns of `object_record_v1_valid` and `hash_policy_v1_supported`, use exported `unit`s in place of `@allow(primitive_api)`. Conditions read `.value`, because of the seed bug recorded in `doc/08_tracking/bug/seed_bool_unit_always_truthy_in_condition_2026-11-26.md`.

**Named gap, not fixed here:** no synchronous SOSIX filesystem owner exists (`std.nogc_sync_mut.sosix` covers env, process and temp only). The store and SCV both use the typed std `io.file_ops` owner, with no direct `rt_*`. Moving them to SOSIX needs a sync SOSIX fs surface first.

### Lane A — SCV adapter (after Lane 0)
This lane closes the architecture Phase 1 exit evidence: SCV references store objects through a read-only adapter, legacy `sha256_<hex>` objects import with their identity preserved, and two clients share one published object.

Module `src/lib/nogc_sync_mut/storage/scv_adapter_v1.spl` (imports no `std.scv`):
```
pub struct ScvImportV1: status: text, reason: text, object_key: text, reused: StoreFlagV1
pub struct ScvPinV1:    status: text, reason: text, pinned: StoreCountV1, skipped: StoreCountV1
pub fn scv_adapter_v1_store_root(repo_root: text) -> text            # "<repo>/.scv/store"
pub fn scv_adapter_v1_import_bytes(repo_root: text, legacy_id: text, bytes: [u8]) -> ScvImportV1
pub fn scv_adapter_v1_import_chunk(repo_root: text, legacy_id: text) -> ScvImportV1
pub fn scv_adapter_v1_open_projection(repo_root: text, legacy_id: text) -> StoreOpenV1
pub fn scv_adapter_v1_pin_reachable(repo_root: text, reachable: text, owner: text) -> ScvPinV1
```
Identity: ingest uses policy `sha256`, so the store key equals the legacy id. An id that is not `sha256_` + 64 lowercase hex, a digest mismatch, or any other returned key (including `_c<n>`) is `rejected`. Consumer: `scv_gc_command` calls `pin_reachable` (owner `scv`) right after the reachable set is computed, only when `<repo>/.scv/store` exists; no SCV write path is hooked (lazy import at GC time). Pins are append-only, so each call writes generation `g+1` as `scv-gc-<g>-<n>` (<= 16384 refs per pin) and then releases the older `scv-gc-*` generations.

### Lane B — Phase 2 storage view on the host (after Lane 0)
This lane provides an immutable base with a private upper layer over store objects, plus filesystem save/load and reference clone, all proven with real temp directories on this Windows host. Its signatures are fixed before dispatch.

Signatures (module `std.nogc_sync_mut.storage.storage_view_v1`; units `ViewBytesV1: i64`, `ViewFlagV1: bool`, `ViewCountV1: i64`; reuses `StoreGenerationV1`):

- `storage_view_v1_create(store, view_root, view_id, base_root, base_generation: StoreGenerationV1, quota: ViewBytesV1) -> ViewHandleV1` (`base_root` "" = empty base; lifecycle journal written first)
- `storage_view_v1_open(store, view_root, view_id) -> ViewHandleV1`; `storage_view_v1_add_volume(view, name, host_dir, writable: ViewFlagV1) -> ViewHandleV1`
- `storage_view_v1_write(view, rel_path, bytes) -> ViewWriteV1`; `storage_view_v1_read(view, rel_path) -> ViewReadV1` (upper, then base manifest)
- `storage_view_v1_save(view, root_name, expected: StoreGenerationV1) -> ViewSaveV1`; `storage_view_v1_load(store, view_root, view_id, root_name) -> ViewHandleV1`
- `storage_view_v1_clone(src, new_view_id) -> ViewHandleV1` (rejects `clone-dirty-upper`); `storage_view_v1_destroy(view) -> ViewDestroyV1` (idempotent, journal-driven)

Manifest is an SDN object (`kind: container-view-manifest`, sorted unique `{path,key,length}`); the root lists the manifest key first, then all file keys.

### Blocked on this host (honest stopping line)
Phase 2 native memory/confinement providers (Docker on Windows per owner engine mapping, Podman, Jail, Seatbelt), Phase 3 SimpleOS shared pages/PMM, Phase 4 non-Windows provider qualification, and Phase 5 benchmarks at scale produce no evidence on this host. Each needs its target host or the QEMU/board lanes (`.claude/rules/board-runnable.md`).

## Increment 3 Lane E — Windows hard memory cap evidence

Module `src/lib/nogc_sync_mut/io/windows_memory_cap_probe_v1.spl` (no new FFI; wraps `windows_process_owner` start-with-memory / poll / peak-before-collect / collect). Non-Windows hosts return `Err("unsupported-host")`.

- Units: `WindowsJobMemoryBytesV1: i64`, `WindowsProbeExitCodeV1: i64`, `WindowsProbeFlagV1: bool`, `WindowsProbeTimeoutMsV1: i64`.
- `windows_memory_cap_probe_run_v1(WindowsMemoryCapProbeRequestV1) -> Result<WindowsMemoryCapObservationV1, text>` (observation also carries `program` for the evidence digest).
- `windows_memory_cap_verdict_v1(under, over, baseline) -> WindowsMemoryCapVerdictV1` (`Enforced | NotEnforced(text) | Inconclusive(text)`).
- `windows_container_capability_report_v1(verdict, under, over, provider_version) -> ContainerCapabilityReportV1`: `memory_hard_limit` + `job-commit` accounting and `evidence_revision = "job-commit:<sha256>"` only when Enforced; otherwise accounting empty and `evidence_revision = "unaffirmed:<sha256>"`. limit_update/reclaim always false.

Measured 2026-11-26 (Windows 11, child `simple-local-20261125.exe run test/fixtures/container/alloc_mb.spl <N MiB>`): idle peak 175067136; cap 276824064 (264 MiB, must be 4096-aligned or owner readback fails); under N=48 peak 208805888 exit 0; over N=256 peak 310333440 exit 3221226505 (0xC0000409), no marker; uncapped baseline N=256 peak 444280832 exit 0. Verdict Enforced.

Finding: on denial `PeakJobMemoryUsed` overshoots the cap by ~33.5 MB (one allocator growth step), so the over-cap check allows cap + 64 MiB; the under-cap peak must be strictly <= cap. Spec: `test/01_unit/lib/nogc_sync_mut/io/windows_memory_cap_probe_v1_spec.spl`.

Lane E review fixes (2026-11-26): `windows_container_capability_report_v1(under, over, baseline, provider_version)` now derives the verdict itself (no caller-supplied verdict); evidence digest binds program path, sha256 of the binary bytes, under/over/baseline peaks and exit codes, and over stdout. Enforced additionally requires `over.peak >= cap` and `over.peak > under.peak`. `readback_ok` is true only for a positive cap (cap 0 has no readback); `host_arch` comes from the host. Error paths after start cancel and collect the child. Near-cap measurement (cap 276824064): N=124 peak 276021248 ok; N=128 peak 310341632 completed in one run and died 0xC0000409 in another; N=160 peak 310374400 died. Outcome near the cap is nondeterministic and the peak overshoot is bounded at ~33.5 MB, so the 64 MiB tolerance is kept as measured.
