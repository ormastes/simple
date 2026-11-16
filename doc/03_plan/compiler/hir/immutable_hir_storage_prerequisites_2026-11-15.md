# Immutable HIR storage prerequisites

Date: 2026-11-15 (KST). Status: bounded source assessment; implementation and executable acceptance remain outstanding.

Inspected draft: `e64528d863ed36db07d0dc4e48716af6c091da5e`.
Compared release: `cdba81fc9cc52684f7de4c27ed3849bc83a138b7`.
The five implementation owners below have no diff between these revisions. Line references describe the pinned draft, not future heads.

Governing plan: [Immutable HIR / TargetHIR / MIR](immutable_hir_targethir_mir_refactor_plan_2026-11-03.md), especially P1 and lifecycle sections. Related entrypoint prerequisite: [mandatory MIR target session inventory](mandatory_mir_target_session_inventory_2026-11-15.md).

## Evidence and limits

| Owner | Observed contract | P1 implication |
|---|---|---|
| `src/compiler/20.hir/hir_lowering/types.spl:43–47,82–86,1366–1372` | Recognizes `Immutable`, `RevisionImmutable`, and `FrozenImmutable`; lowers their storage type to underlying `T`. Records annotated symbols for diagnostics. The comment explicitly permits other mutable aliases. | The names and read-only access checks do not establish deeply frozen storage, exclusive ownership, or revision retention. Live `Immutable<T>` intentionally permits other writers; that behavior is not an existing-view design bug. |
| `src/compiler/20.hir/hir_lowering/statements.spl:491–532,1103–1104,1162–1165` | Checks writes rooted in tracked symbols and direct mutable bindings from revision/frozen handles. Registration shown here follows explicit handle annotations. | These checks alone do not prove transitive alias safety through extraction, unannotated bindings, calls, or returns. No lifetime pin follows from this symbol table. |
| `src/compiler/20.hir/target_hir/hir_freeze.spl:15–48` | Stores serialized text with a digest; chooses canonical encoding when available, otherwise legacy encoding. Reading verifies the digest and decodes a fresh mutable `HirModule`. | Serialization detaches the stored payload from the source module. This is a serialization-copy boundary, not a shared immutable semantic arena or a serialization-free lowering input. |
| `src/compiler/20.hir/target_hir/hir_snapshot.spl:6–26` | Snapshot identity contains module name, content digest, and generation, with basic validation and equality. | An identity record does not own or retain semantic storage and does not prove semantic target portability. |
| `src/compiler/20.hir/target_hir/target_hir_resolution.spl:16–27,106–110` | Builder and result are ordinary structures containing arrays; freeze assigns `builder.resolved` into result `layouts`. | No sealed ownership transfer, backing-array alias revocation, or private immutable container interface is demonstrated here. This is a source-contract gap, not evidence of an observed runtime race. |

`test/01_unit/compiler/semantics/revision_frozen_immutable_spec.spl:57–65,103–113,127–134` exercises scalar struct copies and selected diagnostic behavior. The read-only-alias case checks that alias creation is accepted, not that all later mutation routes are blocked. `test/01_unit/compiler/hir/hir_snapshot_freeze_spec.spl:27–46` exercises serialized snapshot detachment, independent decoded copies, and digest tampering. These tests do not establish nested collection/class alias isolation, concurrent publication, or retained-reader lifetime safety.

This assessment inspected the five owners and the two focused test files. No tests, compiler builds, runtime lifetime experiments, or whole-repository enforcement audit were performed. It does not assert that no relevant runtime primitive exists elsewhere; an implementation must identify and qualify its actual owner before reuse.

## Next implementation boundary

Implement a sealed semantic-storage owner before treating an annotated `HirModule` as deeply immutable. Builder-only mutation must end at admission. Admission must consume exclusive construction ownership or explicitly detach storage when exclusivity cannot be proven. The returned read handle must retain storage for its lifetime and must not expose mutable backing containers through field/index reads, calls, or returned values. The same ownership mechanism should seal resolution arrays; adding another optional facade is insufficient.

Begin with one representative HIR region containing nested arrays, dictionaries, and referenced objects. Existing symbol diagnostics may support the API, but cannot substitute for ownership and storage guarantees. Preserve intentional live-view behavior; do not redefine all `Immutable<T>` values as permanent snapshots. Do not rename the current serialized snapshot a shared frozen arena or remove its validated compatibility path before qualification.

## Executable acceptance required

1. Retain builder aliases to nested arrays, dictionaries, and referenced objects before admission. Attempt mutation afterward; mutation must be rejected or affect only detached private storage, with admitted content unchanged.
2. Try field/index extraction, unannotated aliases, mutable calls, and function returns from admitted readers. Every route that could recover write access must be rejected or return an independent owned copy; ordinary reads must remain usable.
3. Release the producer while retaining a reader, then read the admitted region. Storage must remain valid until the final owning reader releases it; validate the actual lifetime mechanism rather than only a model.
4. Read the same admitted region repeatedly and from two target consumers. Instrument storage identity and codec calls: readers must share admitted semantic storage without an encode/decode cycle per read.
5. Retain a resolution builder and attempt to alter an admitted overlay. The admitted values must remain unchanged and consumers must have no writable backing-array access.

All five criteria are **UNEXECUTED**. Full HIR graph conversion, semantic witness completeness, concurrent release/acquire publication, cache admission, and Stage 3/native qualification remain separate requirements. Passing this bounded increment would close an ownership prerequisite, not complete P1–P8 or authorize default rollout.
