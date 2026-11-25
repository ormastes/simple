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
roots/<name>.sdn                  # root manifest pointer (atomic replace, generation-checked)
pins/<pin_id>.sdn                 # retention pin: owner, refs, generation
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

**Roots:** manifest text lists object keys (one per line, SDN header with `generation`). `publish_root` enforces the expected generation (0 = create-only via no-replace; >0 = replace only if current generation matches), so root updates are compare-and-swap.

**GC:** reachable set = union of object keys referenced by all roots and pins. Default dry-run lists unreachable keys; `dry_run: false` moves them to `quarantine/<date>/` (SCV discipline — never unlink). Live kernel mappings and in-flight staging are represented by pins; a pin is never collected by GC.

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

Increment 1 implemented and verified: 6 specs / 56 examples green on the Windows host. `immutable_store_v1` moved to `src/lib/nogc_sync_mut/storage/` (it does file I/O; `common/` is pure). Docs moved under `doc/<phase>/platform/container/`. Spec mirror generated. Lands via PR to `release/1.0.0`.
