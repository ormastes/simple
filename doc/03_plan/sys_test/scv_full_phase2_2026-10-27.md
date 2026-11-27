# SCV full-system and phase 2 acceptance design

Date: 2026-10-27. Status: planned scenarios; all runtime execution NOT RUN in this lane.

The [master plan](../app/tools/scv_sdn_solver_gateway_master_plan_2026-10-26.md) defines the full 87-scenario suite; the [compiler plan](../app/tools/simple_scv_compiler_tldr_build_cache_implementation_plan_2026-10-27.md) adds 28 scenarios. The tables below preserve every ID and oracle. Existing tests and source helpers are prerequisites only. No scenario is marked passed from an existing filename, PR title, print-only command, or placeholder.

## First independent oracles

1. Source: verified move on one side, independent body edit on the other. Assert exact bytes and identity/effects; include copy and stale-body negative controls.
2. DB: distinct offline column additions, rename, then old-schema update. Assert ColumnUid addressing/schema/constraints, explicit mapping/refusal and original drafts retained.
3. Compiler: request the same verified OBJ twice. Assert zero parser/HIR/MIR/OBJ/link work on the second request and unchanged output materialization state.
4. Absence: create a relevant formerly missing import/name in a permitted search domain. The old negative witness must fail, then warm result must agree with cold symbols/layout/runtime behavior.

## Typed evidence and scenario generation

Use the shared setup/capture/exercise/evidence/assert steps and helper names from the [detail design](../../05_design/scv_full_phase2_2026-10-27.md). Each later executable scenario must call the real capture/compiler/cache/runner owner; missing implementation fails explicitly. Store executable `.spl` specs under `test/03_system/app/scv/feature/`, never under `doc/06_spec`. Generate manuals only from actual executable specs/evidence; this planning document is not a generated execution manual.

Evidence binds test/scenario ID, actual implementation/toolchain/provider/schema/config revision, snapshot root and capture barrier/coverage, exact input and directory/query witnesses, semantic action/receipt, actual cold/warm output digests, independent expected symbols/layout/runtime result, observed per-stage task counts, process exit/diagnostics, injected faults and actual completion. Record not_run/skipped/unavailable/incomplete/cancelled/fail separately. A passing subset is incomplete evidence.

Runtime negative controls include corrupt witness, dropped event, colliding local ID, modified overlay, changed pointcut scope, stale producer, failed publication and lost acknowledgement. Recover corrected inputs and compare with an independent cold oracle. Same-digest IR round trips alone do not prove compiler consumption semantics.

## Full SCV acceptance crosswalk

| Scenario | Required outcome | Primary tasks |
|---|---|---|
| `AT-C01` | Parse all shipped .sdn configs/profiles/manifests with bounded full SDN; nested maps, inline arrays using =, and named tables work. | `SCVN-C01`, `SCVN-C04` |
| `AT-C02` | Duplicate keys, wrong table widths, unsupported mandatory fields, malformed scalars, and byte/depth/node limits reject precisely without changing the last accepted config. | `SCVN-C01` |
| `AT-C03` | Route identical .sdn extensions as config, schema, and data; ambiguous matches and protected-file renames cannot silently select a weaker solver. | `SCVN-C02`, `SCVN-C05` |
| `AT-C04` | A branch that changes its solver/policy cannot use that proposed policy to approve itself; local or CLI overrides cannot enable denied capabilities. | `SCVN-C03`, `SCVN-C05` |
| `AT-C05` | An artifact/ABI/query/profile upgrade changes the effective derivation key; restoring historical raw bytes does not require the upgraded provider. | `SCVN-C04`, `SCVN-O04` |
| `AT-P01` | Missing required plugin blocks verified promotion but not ordinary save/private checkpoint; DB solver absence never falls back to an accepting text merge. | `SCVN-P01`, `SCVN-P03` |
| `AT-P02` | A solver attempts network access, live-file writes, shell execution, clock/random input, or alias allocation; the host denies the operation. | `SCVN-P02` |
| `AT-P03` | Crash, timeout, cancellation, oversized output, malformed result, and cyclic object references return explicit failure/partial states without publishing. | `SCVN-P02`, `SCVN-P04` |
| `AT-P04` | Two solvers propose overlapping edits or inconsistent mappings; the host detects the conflict instead of accepting whichever finishes first. | `SCVN-P03` |
| `AT-P05` | Same pinned inputs yield the same deterministic candidate under varied scheduling; resource-limited outcomes remain explicit and are not reusable successes. | `SCVN-P03`, `SCVN-R03` |
| `AT-P06` | A solver forges validation receipts or says all checks passed; independent producer/subject/required-manifest checks reject it. | `SCVN-P04`, `SCVN-R02` |
| `AT-P07` | A stored manual resolution is reused only with valid base/entity/schema/policy/provider bindings; changed preconditions force revalidation. | `SCVN-P05` |
| `AT-S01` | Move a file on one side and edit an unchanged function on the other; preserve file/entity identity and both intended effects. | `SCVN-S01`, `SCVN-S02` |
| `AT-S02` | Copy, competing rename, rename-delete, and repeated identical declarations do not collapse unrelated identities or lose a branch. | `SCVN-S01`, `SCVN-S03` |
| `AT-S03` | Merge histories with multiple relevant parents or ambiguous base ancestry; no first-parent shortcut erases relevant lineage. | `SCVN-S01`, `SCVN-S03` |
| `AT-S04` | Formatter changes and independent syntax-node changes align without dropping comments/directives or changing ordered constructs. | `SCVN-S03` |
| `AT-S05` | Side-effecting imports, macros/static conditions, and signature/caller incompatibility cannot be accepted solely because syntax parses. | `SCVN-S03`, `SCVN-S04` |
| `AT-S06` | Empty files, binaries, NUL-containing payloads, invalid UTF-8, and no-final-newline inputs survive generic storage; source-only validators do not govern all domains. | `SCVN-O01`, `SCVN-S04` |
| `AT-S07` | Invalid temporary code is saved and checkpointed; verified promotion/build selection blocks under policy without deleting or rewriting the private bytes. | `SCVN-S04`, `SCVN-E06` |
| `AT-S08` | Selective undo of a prior logical change preserves unrelated later edits or raises a typed conflict. | `SCVN-S05`, `SCVN-P05` |
| `AT-E01` | A failed cp/mv command or an agent command merely constructed but not executed cannot become a verified operation. | `SCVN-E01`, `SCVN-E02`, `SCVN-E04` |
| `AT-E02` | Atomic-save replacement, case-only rename, cross-volume copy/delete, hardlinks, and reused inode/file IDs are handled without false logical identity. | `SCVN-E02`, `SCVN-E05` |
| `AT-E03` | A real editor connection applies versioned edits/refactors end to end; stale buffers and disconnected half-transactions remain incomplete. | `SCVN-E03` |
| `AT-E04` | Unsupported editor/LLM tool or absent OS hook falls back to byte capture and conservative inference, not missing changes. | `SCVN-E04`, `SCVN-E05` |
| `AT-E05` | Same-size/same-mtime edits, dropped/reordered events, watcher overflow, and restart trigger correct reads/reconciliation. | `SCVN-E05` |
| `AT-E06` | A burst of fine-grained edits is coalesced without one durable revision/build per keystroke; acknowledged intermediate checkpoints are not erased. | `SCVN-E06` |
| `AT-E07` | Build outputs, SCV metadata, and DB projections do not cause build/commit feedback loops or bypass source-change detection for real edits. | `SCVN-E06`, `SCVN-R01` |
| `AT-E08` | Queue overload/disk-full returns an honest capture/durability state; a successful editor save is not falsely acknowledged as a durable SCV checkpoint. | `SCVN-E06`, `SCVN-B03` |
| `AT-D01` | Concurrent additions of different compatible columns merge by stable ColumnUid, irrespective of textual header order. | `SCVN-D01`, `SCVN-D02` |
| `AT-D02` | Independent same-name same-definition columns remain duplicate-intent candidates until an explicit equivalence/migration rule approves coalescing. | `SCVN-D02` |
| `AT-D03` | Same-name different-type/default/constraint additions yield a schema conflict; no timestamp winner or inferred coercion is selected. | `SCVN-D02` |
| `AT-D04` | Column rename/reorder plus row update resolves by ColumnUid; drop/recreate with the same name cannot resurrect old values. | `SCVN-D01`, `SCVN-D03` |
| `AT-D05` | An old-schema writer adds data after migration; explicit adapter succeeds or admission refuses with preserved draft. | `SCVN-D03` |
| `AT-D06` | Absent, null, defaulted, explicitly set, and tombstoned values remain distinct; volatile defaults are not reevaluated on each replica. | `SCVN-D03`, `SCVN-V02` |
| `AT-D07` | Adding a constant-default column avoids rewriting every historical row; old snapshots retain their original schema interpretation. | `SCVN-D03`, `SCVN-D04` |
| `AT-D08` | Manual SDN edits with missing/duplicate identity bindings or stale projection revisions cannot shift values into the wrong columns. | `SCVN-D04` |
| `AT-V01` | Disjoint column edits merge; incompatible scalar edits remain visible alternatives; wall-clock order never silently resolves them. | `SCVN-V01`, `SCVN-V02` |
| `AT-V02` | Observed/add-wins/remove-wins sets behave according to the selected versioned rule under duplicates and arbitrary causal delivery order. | `SCVN-V02`, `SCVN-V05` |
| `AT-V03` | Increments and append-only observations are not lost by scalar-style coalescing; replaying an operation cannot apply it twice. | `SCVN-V02`, `SCVN-E06` |
| `AT-V04` | Two individually valid transactions violate a shared unique, foreign-key, or cross-row constraint together; admission detects the combined violation. | `SCVN-V03` |
| `AT-V05` | A schema/data/source migration publishes only the validated combined candidate; failed validation does not partially settle its constituents. | `SCVN-V04`, `SCVN-R02` |
| `AT-V06` | Field merge-policy change races with old-policy operations; the migration policy handles the race explicitly, not by reinterpretation. | `SCVN-D03`, `SCVN-V02` |
| `AT-V07` | A generated SDN projection is reparsed for round-trip agreement; formatting/comment treatment remains explicit and submitted text remains recoverable. | `SCVN-D04`, `SCVN-O01` |
| `AT-I01` | Counter reservation, power loss, filesystem rollback, and cloned workspace cannot reuse an acknowledged actor-incarnation/counter identity. | `SCVN-I01` |
| `AT-I02` | Wall-clock rollback/skew and matching timestamps neither collide identities nor decide conflict winners. | `SCVN-I01`, `SCVN-V01` |
| `AT-I03` | Two gateway candidates allocate competing sequence values; only the accepted candidate is final, and the loser replans against the new map. | `SCVN-I02`, `SCVN-I03` |
| `AT-I04` | Retry a previously accepted batch: return the same mappings; reuse its ID with a different payload: reject rather than alias another operation. | `SCVN-I02`, `SCVN-I03` |
| `AT-I05` | A Git topic branch receives tentative aliases but never lands; clients cannot observe those numbers as final accepted IDs. | `SCVN-I03`, `SCVN-G06` |
| `AT-I06` | Acceptance succeeds and the reply is lost; authoritative read-back recovers the exact accepted candidate and aliases before acknowledgement. | `SCVN-I03`, `SCVN-G06` |
| `AT-I07` | Stale gateway fences/epochs, unknown aliases, and sparse missing references fail explicitly; alias numbers are never reused for another entity. | `SCVN-I04`, `SCVN-G07` |
| `AT-I08` | Compaction with a long-offline writer retains needed causal metadata, or requires an explicit retired-replica resync; deleted state cannot resurrect. | `SCVN-V05`, `SCVN-I04` |
| `AT-H01` | Official XXH3/BLAKE3 vectors and randomized large inputs match the selected implementation; zero input and valid zero-valued digests are not errors. | `SCVN-H02` |
| `AT-H02` | Lengths around 64-byte and 1024-byte boundaries, unaligned input, and arbitrary supported streaming partitions match one-shot results. | `SCVN-H02`, `SCVN-H04` |
| `AT-H03` | Force each available SIMD/scalar path; results agree. Unsupported ISA/provider requests refuse before execution or select a truthfully tagged supported algorithm. | `SCVN-H02`, `SCVN-H03` |
| `AT-H04` | GXHash major/version/seed/output distinctions are persisted for reusable fingerprints; no fixed-input-size/streaming capability is guessed. | `SCVN-H03` |
| `AT-H05` | Inject XXH3/GXHash collisions for unequal canonical bytes; deduplication, equality, and build caches retain distinct objects. | `SCVN-H01`, `SCVN-O03` |
| `AT-H06` | Multi-hash selection feeds only required/lazy consumers from one capture; failure of a secure provider never silently substitutes a noncryptographic result. | `SCVN-H04` |
| `AT-H07` | Legacy DB SHA-256 v1 signatures/digests remain verifiable after v2 registration; migration does not alter old canonical signed payloads. | `SCVN-H04`, `SCVN-M01` |
| `AT-O01` | All-byte coverage handles punctuation, trivia, BOM, CRLF, errors, missing nodes, and injected-language overlap without omission or duplication. | `SCVN-O01` |
| `AT-O02` | Full and incremental extraction agree after edits that change token spelling/trivia without large structural changed ranges. | `SCVN-O01` |
| `AT-O03` | Every new parsed-source boundary is a complete node/block/sibling boundary; a giant indivisible token streams intact rather than becoming arbitrary chunks. | `SCVN-O02` |
| `AT-O04` | Sharing identical nodes across files/revisions does not merge logical entity identities; moving an occurrence updates only occurrence metadata as appropriate. | `SCVN-O03`, `SCVN-S01` |
| `AT-O05` | Codec/pack changes preserve raw bytes and logical IDs; whole-file BLAKE3 is not confused with a node-Merkle root. | `SCVN-O03`, `SCVN-H04` |
| `AT-O06` | Restore retained history with all parsers/indexes absent; required recipes, dictionaries, and delta bases alone suffice. | `SCVN-O04`, `SCVN-M04` |
| `AT-O07` | Malformed lengths, excessive decompression/reference expansion, cycles, corrupt payloads, and missing dictionaries reject before publication. | `SCVN-O04`, `SCVN-P02` |
| `AT-O08` | GC races active readers, new revisions, unresolved conflicts, and unpublished drafts without removing their sole reconstruction closure. | `SCVN-O04` |
| `AT-O09` | Optional delta/deferred-raw-digest mode obeys depth/verification limits and explicit readiness states; disabling it remains compatible with retained objects. | `SCVN-O05`, `SCVN-M03` |
| `AT-G01` | A real host with no Git installation creates/synchronizes SCV drafts and queries through the gateway. | `SCVN-G01`, `SCVN-G02`, `SCVN-G03` |
| `AT-G02` | Actual cross-host transfer survives interruptions and duplicate uploads, verifies secure object identities, and enforces authorization on cache hits. | `SCVN-G02` |
| `AT-G03` | Disconnect, create local revisions, restart, edit again, and reconnect after upstream advancement without lost work or silent overwrite. | `SCVN-G03`, `SCVN-G06` |
| `AT-G04` | Sparse/unhydrated files are never exported as deletions; an incomplete reference query cannot report complete zero results. | `SCVN-G03`, `SCVN-I04` |
| `AT-G05` | Git round trips preserve supported bytes, modes, symlinks, path semantics, parent projections, and original imported objects where applicable. | `SCVN-G04` |
| `AT-G06` | A publication response is lost or an external writer advances the target; read-back/reconciliation prevents duplicate or stale acceptance. | `SCVN-G05`, `SCVN-G06` |
| `AT-G07` | GitHub merge/squash/rebase produces a new landed identity; the gateway imports the actual result rather than equating it to the submitted head. | `SCVN-G06` |
| `AT-G08` | Private checkpoints and sensitive native metadata do not leak through public Git ancestry, trailers, or automatic draft export. | `SCVN-G04`, `SCVN-C03` |
| `AT-G09` | Gateway failure/restore preserves settled aliases and unexported drafts using native backup; Git-only restore advertises its limitations. | `SCVN-G07` |
| `AT-R01` | Compiler/tests use a frozen candidate; changed OS/CPU/ISA/static settings/dependencies/toolchain invalidate incompatible cache results. | `SCVN-R01`, `SCVN-R03` |
| `AT-R02` | Required-check manifests distinguish not-run/skipped/incomplete/unavailable/cancelled/fail; a passing subset is never complete evidence. | `SCVN-R02` |
| `AT-R03` | Schema-only and data-only changes select DB validation, while mixed migrations include necessary source/application checks. | `SCVN-V04`, `SCVN-R02` |
| `AT-R04` | Concurrent isolated agents edit overlapping source and DB entities; all acknowledged drafts survive, with deterministic or explicit-conflict reconciliation. | `SCVN-R04` |
| `AT-Q01` | Each context item reconstructs at its declared revision/schema and permission scope; mandatory evidence cannot be omitted by a learned policy. | `SCVN-Q01` |
| `AT-Q02` | Repoformer/selective baselines use pinned held-out tasks without future-code leakage and report actual outcomes plus policy/token/time cost. | `SCVN-Q02` |
| `AT-M01` | Crash at each new object/WAL/map/ref/receipt boundary yields a complete old/new state or explicit corruption, never vacuous success. | `SCVN-M02`, `SCVN-B03` |
| `AT-M02` | Legacy and new shadow representations/solvers are compared without changing protected authority; unknown mandatory formats fail precisely. | `SCVN-M01` |
| `AT-M03` | Rollback with later acknowledged drafts retains compatible readers or performs verified export; it does not delete .scv to erase uncertainty. | `SCVN-M03` |
| `AT-M04` | Parser-free object-only restore, upstream-only limited restore, checkpoint restore, corrupt-index rebuild, missing-index recovery, and interrupted-transaction recovery are independently exercised. | `SCVN-M02`, `SCVN-G07` |
| `AT-M05` | Tombstone/alias/journal retention and raw-copy reclamation are tested with offline rejoin and independent restore before irreversible deletion. | `SCVN-M04`, `SCVN-V05` |

## Compiler acceptance crosswalk

| ID | Test | Pass oracle |
|---|---|---|
| SCV-CACHE-01 | Repeat build, same snapshot and output | no-op; zero parser/codegen/link work; no output rewrite |
| SCV-CACHE-02 | Same inputs, deleted output destination | materialize cached OBJ/BIN/LIB; zero compiler/link tasks |
| SCV-CACHE-03 | Unrelated commit / other branch | semantic artifact reused, new exact snapshot receipt |
| SCV-CACHE-04 | Dirty worktree/unsaved editor while commit unchanged | captured new bytes; stale cache rejected |
| SCV-CACHE-05 | Build concurrent with edit/coalescing | capture barrier includes acknowledged edit; build matches frozen snapshot |
| SCV-CACHE-06 | Event overflow/restart/journal hole | coverage unknown, reconcile or fail; never false hit |
| SCV-CACHE-07 | Merge / non-ancestor branch switch | exact changed-path closure; no first-parent blind spot |
| SCV-CACHE-08 | Rename/move across AOP directory scope | old/new paths and effective directory facts correct |
| SCV-CACHE-09 | Previously missing import created | negative witness breaks; new declaration observed |
| SCV-CACHE-10 | Pointcut changes match set and adds type/member | all old/new affected scopes revalidated; generated interface matches oracle |
| SCV-CACHE-11 | Behavior-only advice changes public layout | rejected; no admitted invalid TLDR/OBJ |
| SCV-CACHE-12 | Macro interface/body changes, nested users | only relevant consumers regenerated; reverse index exact |
| SCV-CACHE-13 | Generic use added, removed, repeated or concurrently published | unique demand counts correct; zero demand does not delete pinned artifact |
| SCV-CACHE-14 | Failed/cancelled/stale compile manifest replacement | old admitted manifest retained; no stale publisher wins |
| SCV-CACHE-15 | AST-set with legal import cycle and new file | SCC correct; no edge lost by sort/Bloom |
| SCV-CACHE-16 | xxh3/truncated path ID forced collision | exact canonical equality check; no false alias |
| SCV-CACHE-17 | Multiple digest alias and corrupt remote content | mismatch rejected; SHA/BLAKE identity verified per policy |
| SCV-CACHE-18 | Big-endian host simulation, x86/ARM/RISC-V targets | canonical portable AST/HIR reuse; target HIR/OBJ valid |
| SCV-CACHE-19 | Load binary cache pack in new process | container-ID and stable-entry refs reconstruct, stale pointers never used |
| SCV-CACHE-20 | Crash during manifest/index/receipt publication | replay yields old or complete new root, not half state |
| SCV-CACHE-21 | Embedded vs BuildRunner SRC→OBJ | matching semantic output and dependency read-set; no runner requirement standalone |
| SCV-CACHE-22 | TestRunner reuses OBJ but changes test env/input | build artifact reused; test verdict appropriately re-executed |
| SCV-CACHE-23 | Aggressive cache eviction under pinned main/release/worktree | pinned history and active packs safe; budget reported if infeasible |
| SCV-CACHE-24 | Version migration V1–V4 action keys / new semantic key | old readers valid; cross-commit hit only after complete witness verification |
| SCV-CACHE-25 | Concurrent 100 consumers of one changed TLDR | single admitted producer; no lost wakeups; reverse manifest exact |
| SCV-CACHE-26 | New generated source modifies directory inventory | one admitted new generation, no self-triggering infinite rebuild |
| SCV-CACHE-27 | Symlink/case/Unicode/path-policy change | exact path and search-domain witnesses, sandbox constraints enforced |
| SCV-CACHE-28 | Clean build oracle after partial facet invalidation | same symbol/layout/runtime semantics; only necessary stages executed |

## Verification and handoff gates

Document checks validate relative links, complete crosswalks, dependency acyclicity and exact supplied-document preservation; they do not execute features. Native suites run later with the pure-Simple self-hosted runtime and core/MCP/LSP checks when compiler/core implementation changes.

Executable SSpec, generated manuals and actual native runtime/operational receipts remain open implementation gates. Replace existing fail-fast settlement scenarios with real owner calls before feature verification can pass. Planning review status is separate from runtime NOT RUN.
