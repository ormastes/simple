# Aspect-generated getters/setters: implementation seam and first vertical slice

Revision: 2026-11-14. Source audit pinned to `0aa438444da8f731a8a0d3187fb39ed0800c6eef` on release/1.0.0. Status: architecture accepted by Astra on 2026-11-14, including deterministic helper ownership/private linkage, retained getter result/liveness and the exact P1 profile. Contracts remain unimplemented; this review does not qualify production lowering or public get/set support. No production edits, tests or native qualification by this audit.

## Requirement authority and scope

The active user goal explicitly includes generated get/set operations and implicit generation for selected aspects. Existing selected `doc/02_requirements/feature/node_attributes.md` REQ-002/007/008/010/012/014 and the data plan sections 3.3–3.6 and 9 define logical field operations, managed places, canonical selectors, evaluation/ownership invariants, off mode and explanation. This restores work deferred in the older narrow XRay plan. It does not authorize general call-site weaving, typed value capture, dynamic around advice, object-layout replacement or changing ordinary value classes into node handles.

Final scope retains stored mutable/read-only fields, computed/forwarded properties, compound/nested/indexed mutation, ownership/borrow/atomic rules and SPL/SDN parity. The first implementation packet below is a vertical slice, not a reduced definition of completion.

## Existing owners and gaps

| Owner | Actual current behavior | Consequence |
|---|---|---|
| `10.frontend/core/aop_predicate_parser.spl:45–86` | Text selector extractor requires immediate `(`; get/set/init rejected E1507. | Enabling names alone is invalid; use token-aware shared parser and resolved field predicates. |
| `10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl:208` | Pointcut tokens are serialized with inserted spaces. | Both `get(` and `get (` must traverse one parser; current extractor is unsuitable. |
| `10.frontend/parser_types.spl:642` | `AopAdvice` has pointcut/form/handler/priority/span, no named aspect owner. | Add owner propagation before admitting new get/set declarations. |
| `20.hir/hir_lowering/attr_access_sites.spl` | Post-pass collects opt-in node Read/Write/Init/RMW metadata. | Metadata alone cannot rewrite accesses. Preserve its zero-code-change contract. |
| `20.hir/hir_types.spl:964` | Site has text owner/field/function plus span/ordinal; no canonical field symbol, exact type, mutation authority or place. | Never rewrite by span or short field name. Construct typed operation plans at the actual lowering owner. |
| `20.hir/hir_lowering/_Expressions/accessor_forwarding.spl` | Missing real field can forward to existing get_/is_/set_ methods. Real fields win. Compound forwarding accepts only bare receiver variables. | Forwarding is not generation. Do not reuse it to intercept real fields or change its precedence. |
| `src/app/compiler_schema/node_view_gen.spl:329` | Generates marked semantic view methods from resolved schema/owner binding, plus storage mechanisms. | Reuse identity/provenance and cleanup exclusion contracts; do not build a second schema resolver. Coordinate active node-storage lane before touching this file. |
| `50.mir/_MirLoweringExpr/expr_dispatch.spl:6136` | Field read lowers receiver once, then resolves field/storage/type-specific operations. | Insert selected logical read integration after classification and before the final raw field operation. Preserve special strings, Result projections, option handling and bitfields. |
| `50.mir/mir_lowering_stmts.spl:2275,2672–2737` | Assignment lowers RHS before receiver. Field path preserves trait/Option coercion and isolated-place Move facts before store. | Retain RHS-first order. Insert setter call only after these existing transformations; do not silently bypass NLL facts. |
| `50.mir/mir_data.spl:1386,1774,1881` | Existing typed emit_call, emit_get_field (including type/base cursors), emit_set_field. | Generate native helper bodies with these operations and actual resolved cursor/type metadata. |
| `50.mir/mir_aop_injection.spl` | Existing parameterless/unit advice call and entry/return/instruction injection primitives. | Reuse those primitives. Add a narrow typed logical-access plan consumer rather than another general weaving engine. |

Worktree observation: `/home/yoon/dev/simple-nodestore-20261113` exists (branch `work/lexer-span-followups-20261113` at inspection); LLVM XRay work is separately owned under `/tmp/simple-xray-llvm-runtime-link-20261114`. Root worktree has unrelated work. All future edits require an isolated branch and fresh owner check.

## Contract to freeze

Proposed names are implementation contracts, not currently available APIs:

- `AspectOwnerKeyV1`: declaring module identity plus named aspect declaration identity, never just its unqualified name. Parser, flat-AST bridge, HIR advice, selector/interface digest and catalog must retain it. Existing legacy advice may retain an explicit legacy owner during migration; new get/set declarations require a named owner.
- `LogicalFieldKeyV1`: canonical owner/type declaration identity + exact field declaration identity + instantiated type arguments. Source alias spelling and a dense backend offset are not identity.
- `FieldAccessPlanV1`: operation kind, field key, exact resolved type/qualifiers, original logical site, declaration visibility/authority decision, selected aspect owner/advice order, physical layout/ABI identity and generated target key. Common serialized facts contain no HIR pointer; HIR/MIR owners retain their own typed references until signature construction.
- `GeneratedAccessorArtifactV1`: helper symbol, field key, operation, schema/origin and interface/body digests. The helper lives in a compiler-reserved namespace and cannot collide with a source get_x/set_x method. It is not added to a public export surface or granted more visibility than the source field.
- `get(pattern)` and `set(pattern)` resolve canonical logical fields using the existing Boolean vocabulary. `attr(...)` remains annotation metadata. Internal helper signatures take a typed receiver (and setter value); language advice remains `() -> unit` and receives no captured value.

A generated getter returns the exact field type with its existing copy/move/borrow rule. A setter receives the exact already-coerced field value and mutation-authorized receiver/place; it returns unit. Shared class identity and value-struct mutation are different ABI obligations. Helpers cannot turn a value receiver into a temporary whose mutation is discarded.

## Deterministic helper ownership and private linkage

The compilation coordinator freezes the complete, ordered applicable advice plan before any MIR worker generates a helper. A `GeneratedAccessorKeyV1` binds the logical field key, receiver/field ABI, instantiated types, schema and physical-plan identities, provider/compiler identity, operation and the complete ordered aspect-owner/advice plan (including relevant signature/effect/body digests). Sorting or deduplicating advice after key creation is forbidden. A short helper name is only an index; equality uses the full canonical key.

One `GeneratedAccessorEmissionOwnerV1` entry assigns each key to exactly one compiler-generated companion object in the current compilation. The owner object is keyed by the original field-declaration module identity and generation identity; caller-module traversal order cannot select the owner. The coordinator emits one object per assigned owner, while parallel callers only reference its frozen symbol. This is compiler artifact ownership, not an instruction to mutate an independently built dependency's source or object. Cross-package generation requires the admitted declaration/layout metadata and original legal access route; otherwise the selected operation is rejected before object emission.

The helper has link-unit-visible, hidden/compiler-private linkage, never a language `pub` declaration or layer export. Caller objects use its exact symbol and signature; source name resolution cannot name or call it. A platform that cannot express the required private linker/ABI contract is not admitted. Aspect advice references use already resolved symbols under the same compilation admission; they do not gain source visibility by virtue of helper generation. When no linker-wide common ownership exists (for example separately loaded modules), do not pretend a per-process deduplication guarantee: that configuration needs its own admitted module contract before generation.

This ownership map enters object-cache and link-receipt identity. It prevents two caller workers from defining the same helper, and prevents reusing a helper whose ordered advice, field layout, provider or instantiated ABI has changed.

## Retained values and the first admitted scalar profile

P1 supports only a non-null, resolved, identity-bearing class reference and a direct stored field of exact copyable primitive type: `bool`, `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, or `u64`. The declaration must be non-volatile, non-atomic, non-MMIO and outside bitfield/packed-storage special paths. The field carries no move-only, isolation-transfer or borrow-return obligation. A setter additionally requires the original writable-place/receiver authority. This precise profile is an initial admission boundary; the later packets retain all other selected requirements.

A getter helper loads the field exactly once into a typed result local **before** invoking `after_success` advice. It returns that retained result even if advice changes the underlying field through another legal reference. There is no second load after advice, and advice cannot replace the return value through the parameterless ABI. The receiver loan/reference and the captured result remain live through advice and the return; existing ownership/liveness machinery must represent these obligations, rather than assuming that a parameter unused after the load can be released early.

A setter performs the actual typed store before `after_success` advice and returns only after that advice completes normally. A `before` advice failure prevents the operation. An abrupt exit from `after_success` does not roll back an already committed store or fabricate a completed caller return; it follows the existing language advice/error semantics. Unsupported unwind, destruction/lifetime, or mutable-reference behavior must be diagnosed for the selected profile rather than modeled as success.

## Lowering and advice boundary

1. Resolve the declaration and access permission normally. A selector matching a private field is not authority for an illegal source access or public export.
2. Freeze applicable field-aspect selection before MIR workers. With no explicit accessor generation request and no matching field aspect, keep the existing field lowering path and produce no helper, metadata object, additional branch or trace dependency.
3. On the selected path, evaluate original operands into existing MIR locals exactly once. Reads evaluate receiver once. Assignment retains current RHS-before-receiver order; indices follow their existing owner order. Do not introduce a conventional receiver-first rewrite.
4. Reuse existing resolution/coercion/isolation bookkeeping, including Option handling and Move facts. A selected unsupported place fails explicitly; never continue using an incorrect partial rewrite.
5. Synthesize one typed helper per canonical field operation + admitted instantiation/ABI + applicable advice plan. Its body performs the existing raw GetField or SetField, with compiler marking that prevents recursive logical re-selection. Do not reconstruct field offsets from text.
6. Use existing MIR injection primitives for parameterless before/after_success advice, preserving priority/order/conflict checks. A completed-read observer occurs after the valid value is produced; completed-write occurs after commit. Before semantic advice remains distinct from a successful-operation observation. Normal exit is not Result-success proof or an invented after_error event.
7. Exclude generated accessors and backing storage helpers from ordinary execution matching by default. The logical get/set surface is counted once. Explicit helper-level tracing, if ever offered, must be a separate declared domain.
8. The physical call may inline when semantic advice permits. No blanket no-inline, per-event selector parsing, path hashing or new runtime dispatch layer is introduced. Dynamic observation uses the existing admitted trace path only; static field semantics do not depend on XRay activation.

Do not route the logical helper through `apply_weaving_result` blindly: its current switch is on join-point kind and does not itself supply the required new logical form/placement contract. The small new consumer must dispatch the validated advice form to existing injection primitives, not implement its own instruction mutation engine.

## Precise first implementation packet

P0 (prerequisite): named owner and tokenized field selector representation survive parser/flat AST/HIR/cache round trips. Keep get/set rejection until the actual consumer below is enabled; whitespace fixes apply consistently. Use the existing named-aspect ownership design, not an unrelated new source annotation.

P1 (first end-to-end vertical slice): the exact scalar/reference profile above, getter read and plain setter write, static parameterless before/after_success advice, deterministic single-owner helper emission and compiler-private linkage. Generate helper bodies through MirBuilder, rewrite the original sites, and prove read value/write state and advice order in a real compiled program. Preserve declaration visibility. Explicit generation and implicit aspect-triggered generation share one helper planner; explicit generation uses existing schema/descriptor inputs rather than inventing public methods for every field.

Initially reject selected value-struct receiver paths, nested/indexed writes, bitfields, atomic/volatile/MMIO, move-only/borrow-returning fields, computed/forwarded failures and compound updates until their corresponding place/ABI packet lands. Unselected occurrences remain on their normal existing paths. Those cases remain required final work, not permanent exclusions.

P2: reuse the already evaluated receiver/place for RMW, with one getter plus one committed setter unless an admitted atomic RMW owner supplies a distinct operation. Preserve the existing RHS-first rule. Extend writable place-chain lowering for nested/value-struct/indexed mutation; no get-copy-set or unproved copy-back shortcut.

P3: computed/forwarded/read-only/schema-declared fields, authority/borrow/move/atomic profiles and both interpreter paths; initializer/failure/removal/migration stay distinct. Admit dynamic observation only with actual provider/capability evidence. Complete LSP origin/explanation and producer/consumer cache coverage.

File ownership for P0/P1: parser types/flat advice owner bridge and shared selector parser; new small field-access planner in HIR/semantic owner; new MIR accessor synthesis module; thin hooks in existing Field read and assignment owners; existing driver AOP plan composition; shared generated-artifact/filter metadata; focused specs/native fixtures. Do not modify node storage implementation or unrelated LLVM/Windows provider files.

## Cache and generated-artifact rules

Separate declaration/schema, physical layout, helper interface and advice body digests. Helper identity binds canonical owner+field+operation+instantiation, applicable aspect-owner/selector digest and target ABI. Object/action keys include the generated body and physical plan. An advice-body change may rebuild/reload the relevant helper but cannot reuse an old woven helper. A visibility/type/owner/selector/layout change invalidates affected file TLDRs, directory facts and dependent selection outputs. Runtime recording toggles do not regenerate source helpers. Generated artifacts carry the existing semantic marker/origin so accessor-cleanup tools do not remove them. Serialized compiler facts are metadata, never borrowed HIR memory or runtime mutation authority.

## Required regression packet

- G1: token-aware get/set with spaces/comments/Boolean grouping; malformed/unknown forms reject; named owner preserved through AST/HIR/cache.
- G2: generated helper signature retains exact field type and owner; two classes with the same short field name never share a helper; generic instantiations remain distinct.
- G3: one getter returns actual stored value, one setter changes the original class object; before/after_success handlers fire once in the declared order. Advice remains zero-argument/unit.
- G4: side-effecting RHS and receiver execute exactly once in the original RHS-first order; negative mutation of the planner order must fail the oracle.
- G5: ordinary missing-field forwarding and explicit source get_x/set_x methods retain behavior. Real field access cannot accidentally route to those methods through the new generation plan.
- G6: owner-private field stays inaccessible externally; compiler-generated helper is not an export escape.
- G7: explicit generated read-only property has no setter; construction does not count as set; failed update does not emit successful set.
- G8: matching RMW/nested/value-struct/atomic/borrow forms produce the scoped unsupported diagnostic until their semantic packet is implemented; do not merely match none.
- G9: no aspect/no explicit generation gives identical MIR/function inventory and object/dependency output; no helper/tracing closure added.
- G10: generated helper and backing storage do not cause duplicated execution/get/set events; cleanup retains semantic artifacts and navigation points to original field.
- G11: selector/owner/type/visibility/advice/layout mutations invalidate exactly the relevant cached plans; whitespace-equivalent selector identity is stable; runtime toggle does not alter helper identity.
- G12: two caller modules and concurrent MIR workers share the same frozen helper key and single emission owner; final link contains one definition, no language export, and exact typed references. Changed advice order/provider/layout cannot reuse the old helper.
- G13: getter after_success advice mutates the field through a legal alias; the caller still receives the value captured before advice. Prove receiver/result liveness and one raw load. Setter-after failure preserves the committed store; before failure performs none.
- G14: self-hosted/native and both interpreter access paths agree before broad support is declared. A single scalar pilot is not full feature or Phase 3 proof.

These are proposed tests, not recorded passes. Sidecars: N/A for this read-only design audit. The two post-review ownership/value contracts above incorporate Astra feedback; their proposed names must be frozen in implementation contracts before enabling selectors. Implementation merge owner: root; final architecture/source reviewer: Astra. No production edit should enable E1507 removal without the matching typed field consumer and an exercised end-to-end lane.
