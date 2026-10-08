# Native trait dispatch: item5 implementation contract

Status: partial implementation, not compiled or executed. Selected scope is real dynamic dispatch, as explicitly requested; no one-implementation devirtualization.

## Representation and identity

Plain trait-typed `Named` values and explicit `DynTrait` must share the same representation. Trait identity comes from retained `HirModule.traits` plus provider relocation, never from a method name or the count of implementations. The existing `DynTrait -> Tuple(Ptr<U8>, Ptr<U8>)` is currently only a type mapping and is not an implemented ABI.

Use a data owner plus immutable vtable reference. Data must remain a runtime-owned value, not a pointer into the conversion function's stack. Vtable identity includes canonical trait owner and concrete implementation owner. Method slots are sorted by exact declared method name; reject duplicate/ambiguous slots. A slot retains its full receiver/argument/result ABI and mutability. Method pointers must refer to concrete implementation thunks, never trait declaration symbols.

Conversions are required at function arguments, returns, annotated bindings and aggregate fields. An already matching trait object passes through without being boxed a second time. A concrete conversion requires an explicit matching HirImpl trait identity and all required methods; missing or incompatible implementations fail compilation. Generic methods and unresolved associated/Self-dependent signatures must be rejected explicitly until their object ABI is implemented, rather than erased to guessed i64.

## Dispatch and ownership

Load the receiver's data and vtable, select the declared slot, and emit existing `MirInstKind.CallIndirect` with the explicit data receiver followed by arguments. LLVM and Cranelift must agree on aggregate transport; both backend paths need review and actual execution. Neither global short-name dispatch nor switching on concrete implementation names is acceptable.

Existing classes are reference-like even through ordinary parameters. Value structs copy through ordinary parameters and alias through `me`/`mut`. Trait conversion/parameter copying must preserve those distinctions, including owner-bearing provider session values. A concrete copy thunk aliases class data and uses the existing recursive struct-copy owner for value structs; mutable borrowing passes the same data owner. Isolation and resource metadata must remain attached across conversion and moves. Calling close through a trait must consume/update the same owned receiver as concrete close. This is a required ABI part, not a later cleanup optimization.

The source draft adds typed canonical metadata, relocated provider signatures, method and copy thunks, heap aggregate construction, an indirect slot emitter, and parameter/tail-return/explicit-return/annotated-binding/call-argument/constructor-field hooks. Named arguments evaluate in source order before declaration-order slot placement. Optional fields use the existing Option owner after payload conversion. HIR trait lowering supplies the exact receiver owner that concrete method lowering already supplies. Signature admission checks receiver, argument/result types and receiver mutability; conflicting declaration layouts fail closed.

This initial object ABI explicitly rejects generic/associated/supertrait layouts, resource destructor erasure and isolated ownership transfer. Those are unsupported compiler cases, not changed ownership rules or successful dispatch. Class provider close methods retain their actual shared receiver; language `resource`/`iso` envelopes require additional drop/transfer slots before admission. A conversion creates heap data/vtable envelopes using existing aggregate lowering; there is no static-vtable deduplication or performance qualification. Method pointers use consumer-qualified generated thunk names to avoid duplicate external symbols across modules.

## Source ownership and integration hooks

- Trait lane: `mir_lowering_types.spl`, `_MirLowering/module_lowering.spl`, `_MirLowering/function_lowering.spl`, `_MirLoweringExpr/method_calls_literals.spl`, new trait helpers, regression fixture.
- Enum lane edits separate enum-match regions of `expr_dispatch.spl` and `switch_operators_calls.spl`. Trait changes in this isolated tree only add helper imports, explicit-return conversion, call-argument conversion after declared parameter recovery, and constructor-field conversion. Apply both isolated patches sequentially; do not overwrite either file wholesale.
- The shared conversion contract is `coerce_native_trait_object(local: LocalId, value: HirExpr, expected: HirType) -> LocalId`.

## Source-review checklist before freeze

1. HIR trait receiver context and qualified callable declarations; no bootstrap return-erasure policy changes.
2. Exact module-qualified trait/concrete ownership, provider SymbolId relocation, deterministic method slots and full typed signatures.
3. LLVM and Cranelift heap Tuple transport, function-pointer constants and typed indirect calls; runtime execution still required.
4. Class aliasing versus ordinary value-struct copies and `me`/`mut` borrowing; generated copy lowering must not contaminate outer local metadata.
5. Factory early/tail returns, parameter/binding/field conversions and optional payload wrapping; unknown merged concrete provenance must fail rather than choose an implementation.
6. Two concrete classes through the same ordinary trait parameter (13 assertions), value-struct copy/borrow including place fields, Optional envelopes and outer value-struct copies (26 assertions), missing membership negative, incompatible result-ABI negative and per-argument mutability mismatch negative. No assertion has executed yet.
7. Language resource/isolated transfers, supertraits, generics, inferred branch-merge conversion and performance remain outside this initial admitted ABI. No full provider/application completion claim follows from these sources.

## Evidence and finite qualification

Baseline cf89 minimal HTTP trait fixture fails MIR unresolved `parse_probe_v1`/`close_probe_v1`; retain that evidence. New regression uses two distinct concrete classes through the same plain trait parameter, with runtime-selected construction and distinct values, then exercises mutable close and rejects use after close. Include trait return and field/optional-field shapes because the existing tracked bug reports silently wrong optional-field data.

One reviewed integrated generation is root-owned. No compiler rebuild or source execution has been run by this lane. Required results are actual LLVM and Cranelift binaries and outputs, plus wrong-implementation rejection; source inspection is not a PASS.

The first bounded source review found two P1s: slot metadata lost non-receiver parameter mutability, and constructor/Optional storage could alias value-struct payloads. The source repair retains and compares every parameter's mutability and funnels ordinary parameters and place storage through a common copy owner. Optional copy branches on the enum discriminant before extracting or copying Some; None is preserved. Review and native execution of this correction remain pending. A proposed DynTrait-relocation finding was withdrawn after confirming the existing base implementation already relocates its symbol ID.

The final source repair also routes trait-bearing fields through that copy owner when an outer value struct is copied. Thunk generation saves, clears and restores per-function local type/Option/nil/runtime-value metadata so its temporary local IDs cannot contaminate the enclosing function. Resource-owner implementations and direct resource-bearing method signatures are rejected until an erased drop ABI exists. Native execution remains unrun; these are reviewed-source candidates, not qualified fixes.

Final bounded source review found no remaining P0/P1 in the reviewed corrections. Its P2 outer-Optional fixture limitation is addressed in source by directly mutating an unwrapped payload through a mutable Optional parameter and checking both original and copied values before replacement. This assertion is unexecuted. Only diff whitespace validation has run; compiler checks, native fixtures, core/MCP smoke, broader gates and release qualification remain unrun. The commit is an integration candidate, not a verified landing.
