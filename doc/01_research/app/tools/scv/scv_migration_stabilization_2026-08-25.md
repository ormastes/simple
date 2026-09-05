# SCV Migration: Stabilization Without Risking the Repository

**Date:** 2026-08-25
**Companion:** `scv_v2_final_report_2026-08-25.md` (architecture); this document covers how to migrate to it safely.
**Status:** research / migration strategy

Yes. For stabilizing SCV without risking the repository, make SCV non-authoritative for a fairly long period and use redundancy at several independent levels.

Change to the original proposal #1: GitHub and the SCV server should not be equal peers initially. **GitHub/Git is the recovery authority; SCV is a shadow system.**

## Recommended stabilization architecture

```text
                          developer
                             │
                             ▼
                    ┌─────────────────┐
                    │ SCV/jj workspace│
                    └────────┬────────┘
                             │
                  implicit snapshots
                             │
              ┌──────────────┴──────────────┐
              ▼                             ▼
        Git/jj canonical                SCV shadow
        repository                     repository
              │                             │
              ▼                             ▼
          GitHub                       SCV server
        remote #1                     remote #2
              │                             │
              │                       semantic DB
              │                       entity graph
              │                       op history
              │                       snapshots
              │                             │
              └──────────┬──────────────────┘
                         ▼
                  periodic backup
                         │
                immutable checkpoint
```

The critical rule during stabilization:

> An SCV failure must never make an existing Git commit unreachable, modify an existing Git object, or prevent reconstructing the repository from GitHub alone.

Git's object model is the safety anchor: `git fsck` verifies object validity/connectivity, and Git's own manual recommends independent backups as the primary defense against corruption.

## 1. Two servers: yes, but asymmetric

```text
GitHub
    canonical public history
    must always be independently cloneable

SCV server
    SCV implicit history
    entity identities
    semantic indexes
    parser trees
    operation log
    Git↔SCV↔jj mappings
```

During early development SCV must never directly rewrite GitHub history. Instead:

```text
SCV explicit commit → validate → Git/jj commit → git fsck → push GitHub
  → verify remote → SCV records "Git commit X successfully published"
```

The SCV server can fail completely and `git clone GitHub` remains the recovery baseline.

Three copies (3-2-1 principle):

- A. local working repository
- B. GitHub canonical repository
- C. SCV backup/checkpoint repository — preferably on different storage/machine from A

## 2. Periodic DB saves: yes, but don't merely copy a live database

Don't `cp scv.db backup/` while it is being mutated unless the database guarantees that snapshot mechanism. Instead, `scv checkpoint` produces an immutable, content-addressed checkpoint:

```text
checkpoint_0042/
    manifest
    repository_view
    operation_heads
    changes
    entity_graph
    parser_registry
    git_mapping
    jj_mapping
    db_snapshot
    hashes

CheckpointId = hash(canonical checkpoint manifest)
```

Schedule:

| Level | Cadence |
|---|---|
| implicit operation journal | continuously |
| local checkpoint | 5–15 min |
| verified checkpoint | hourly |
| full checkpoint | daily |
| off-machine checkpoint | daily |
| long retention | weekly/monthly |

Separate what must be backed up from what is rebuildable:

```text
MUST BACK UP                 REBUILDABLE
────────────────────         ────────────────────
operations                   parser CST cache
logical ChangeIds            semantic indexes
FileIds                      search indexes
EntityIds                    BM25
lineage                      temporary diff indexes
conflict objects             performance caches
Git/jj mappings
implicit snapshots not exported to Git
```

`scv rebuild-index` reconstructs the right column. This dramatically reduces the state that can permanently damage SCV.

## 3. Recovery tool: a first-class subsystem

Implement recovery before making SCV authoritative:

```text
scv doctor
scv fsck
scv recover
scv rebuild
scv checkpoint
scv restore
scv compare-backend
```

`scv doctor` — cheap health check:

```text
Git objects                OK
Git refs                   OK
jj operation heads         OK
SCV operation heads        OK
SCV DB                     OK
object hashes              OK
Git↔SCV mapping            OK
jj↔SCV mapping             OK
entity DB                  OK
parser indexes             stale (rebuildable)
```

`scv fsck --full` — expensive verification of all object hashes, references, trees, commits, operation DAG edges, ChangeIds, EntityIds, checkpoints, packs, remote mappings. Also run `git fsck --full --strict` rather than pretending SCV can verify Git better than Git itself.

## 4. Backend differential verifier

Possibly the single most useful stabilization tool: `scv verify-backends` independently obtains tree views from Git, jj, and SCV and compares paths, modes, file bytes, parents, commit mapping, bookmarks, heads.

Required invariant:

```text
canonical Git tree == jj exported Git tree == SCV exported Git tree
```

SCV semantic information need not match (Git has none), but the SCV exact-byte tree must. Run after every important operation during shadow development.

## 5. Use jj's operation log as an independent recovery layer

Jujutsu records modifying operations in an operation DAG and supports undo and restoring to an earlier operation; its content-addressed operation/view design tolerates concurrent operations without corruption. So initially there are six independent recovery mechanisms:

```text
Git history + Git reflogs + jj operation log + SCV operation log
  + SCV implicit snapshots + SCV checkpoints
```

A bug must defeat all of them.

## 6. Never update objects and HEAD in the same unsafe operation

Write-new-then-publish transaction model:

```text
write Content objects → fsync
write Tree            → fsync
write Commit
write Operation
validate everything
write new head marker → fsync
remove old head marker
```

Everything before final pointer publication is unreachable immutable data. A crash yields OLD STATE or NEW STATE, never half of each. This mirrors jj's operation-store design (content-addressed operation/view objects, head files, stale heads reconciled later). SCV already has content-addressed objects, so strengthening the mutable pointer protocol is far easier than redesigning the store.

## 7. WAL for the small mutable DB

```text
BEGIN operation=823
  old_head=... expected_git=... expected_jj=...
WRITE FileId ...
WRITE EntityId ...
WRITE lineage ...
WRITE mapping ...
COMMIT operation=823
```

On startup: complete transaction → verify/apply; incomplete → rollback/reconstruct.

Better: **make the database a materialized view of an append-only event log.**

```text
events/op000001, op000002, ...  →  materialize  →  scv.db
```

Then `rm scv.db && scv rebuild-db` is a valid recovery. Far safer than making SQLite/SDN the only source of entity identity.

## 8. Make every semantic decision auditable

Never store only `E19 → E19`. Store:

```text
identity_match
    old = E19@R71
    new = E19@R72
evidence:
    same_file_event       1.00
    subtree_similarity    0.97
    signature_similarity  0.92
    parent_similarity     1.00
    reference_similarity  0.88
decision:   move_rename
confidence: 0.974
algorithm:  identity-v3
```

If identity-v3 has a bug: `scv identity re-evaluate --algorithm identity-v4` without losing underlying history. Semantic identity is inherently more heuristic than byte identity.

## 9. Never garbage-collect aggressively during stabilization

`scv gc` defaults to dry run. Actual deletion requires:

```text
scv gc --prune --checkpoint=<verified checkpoint>
```

plus Git fsck OK, SCV fsck OK, checkpoint OK, remote backup OK, retention period passed. Retain unreachable objects 30–90 days initially. Storage is cheap compared with a GC reachability bug deleting the only copy of an implicit snapshot.

## 10. Periodic Git bundles as another independent backup format

```text
daily/
    git-2026-08-25.bundle
    scv-2026-08-25.checkpoint
```

Verify with `git bundle verify` and `scv checkpoint verify`. A bundle lacks working-tree/index/config state; SCV checkpoints cover SCV-specific state.

## 11. Test recovery, not merely normal operation

For each SCV operation, kill the process at each crash point:

```text
snapshot
 1 after content write
 2 after tree write
 3 after commit write
 4 after DB WAL write
 5 after operation write
 6 before HEAD publication
 7 after HEAD publication
 8 before WAL commit
 9 after WAL commit
```

Then: restart → `scv doctor` → `scv recover` → `scv fsck` → `git fsck` → `scv verify-backends`. All must produce a valid old or new state.

Same for: disk full, short write, permission denied, corrupt DB, corrupt index, deleted HEAD, deleted parser cache, duplicate operation head, watcher overflow, machine reboot, SCV server unavailable, GitHub unavailable.

This is worth more to stabilization than adding VCS features.

## 12. Recovery levels

| Level | Action |
|---|---|
| 0 | rebuild derived indexes (parser, search, semantic cache) |
| 1 | rebuild DB from operation/event objects |
| 2 | reconstruct SCV heads from operation DAG |
| 3 | reconstruct SCV from jj + Git |
| 4 | clone GitHub, import Git history, restore SCV checkpoint, replay SCV events after checkpoint |
| 5 | GitHub only — source history recovered, semantic history partially lost |

Even level 5 must leave a completely usable repository.

## Recommended stabilization stages

| Stage | GitHub | jj | SCV | Allowed risk |
|---|---|---|---|---|
| S0 observe | authoritative | authoritative workflow | read-only | none |
| S1 shadow | authoritative | authoritative | writes shadow DB | SCV can be deleted |
| S2 implicit | authoritative | authoritative | owns implicit snapshots | only implicit history at risk |
| S3 verified semantic | authoritative | authoritative | identity/change graph trusted | byte history still independent |
| S4 dual-write | authoritative | authoritative | native objects written too | compare every operation |
| S5 native shadow | authoritative | comparison oracle | native history operates | no public authority |
| S6 native | replicated | compatibility backend | authoritative | production |

The promotion criterion is not "tests pass." S4 → S5 should require roughly:

```text
10M+ randomized operations
100k+ crash-injection runs
zero unrecoverable corruptions
zero byte-tree divergences
large repositories: Git == jj == SCV
30+ days real shadow usage
restore tests:
    GitHub only             PASS
    checkpoint + Git        PASS
    SCV objects only        PASS
    corrupt DB              PASS
    missing indexes         PASS
    interrupted transaction PASS
```

## Implementation priority (stability before features)

1. `scv checkpoint` / `checkpoint verify`
2. `scv doctor`
3. stronger `scv fsck`
4. append-only operation/event journal + WAL
5. `scv rebuild-db`
6. `scv verify-backends` comparing Git ↔ jj ↔ SCV byte trees
7. GitHub canonical + SCV shadow server replication
8. automatic Git bundle + SCV checkpoint backups
9. crash/fault-injection harness
10. conservative quarantine GC
11. `scv recover` with the five recovery levels
12. only then allow SCV to become authoritative

Resulting invariant:

```text
                  SCV CAN BREAK
                       │
          ┌────────────┼─────────────┐
          ▼            ▼             ▼
      corrupt DB   broken parser  bad identity
          │            │             │
          └────────────┼─────────────┘
                       ▼
                source is safe
                jj history safe
                GitHub history safe
                SCV reconstructable
```

Make losing SCV cheap before trying to make SCV impossible to lose.
