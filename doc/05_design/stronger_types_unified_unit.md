# Simple Stronger Types: Unified `unit`, Effects, Protocol States, and LSP

## Follow-on final design, refactoring, and migration plan

**Date:** 2026-11-05  
**Document revision:** 1.0 — a design revision, not a deployed language or ABI version  
**Repository:** `ormastes/simple`  
**Status:** Proposed implementation plan with scoped source observations and primary-source research. No compiler changes, test execution, or performance measurements are claimed.  
**Inspected source revision:** `97700b29e10675867891503f1e634b50a192356d`. This is a pinned snapshot, not a claim about the latest branch.

> **Final direction:** Use `unit` as the single declaration keyword for measurement families, nominal IDs, custom value wrappers, and refinement-constrained values. Reuse the same machinery for zero-payload state markers. Keep ordinary builds lightweight; run expensive verification and diagnostic instrumentation only in `debug`, `invest` (investigation/inspection), and `ci`. Improve the existing type/effect/contract implementation and the shared LSP/CLI/MCP semantic tooling, rather than adding parallel systems.

### Scope and relationship to the earlier report

This is a **new follow-on report**, covering the stronger-type discussion after the previous safety/refactoring report. It does not embed, append, or reproduce that report. The earlier panic-source matrix, `nil`/optional representation design, general error-fixer architecture, and complete AST-edit transaction protocol remain separate.

The following new decisions supersede earlier conversation suggestions:

1. Do not retain `unit`, `newunit`, and `newtype` as three permanent declaration keywords. Migrate the latter two into `unit`.
2. Do not introduce a separate `refined`, `state`, `session`, or `capability` keyword, nor a new mandatory `requires` or `no_panic` annotation.
3. Merge implementation and declaration surfaces, **not distinct meanings**. An alias, nominal ID, measured quantity, predicate, and resource state are not interchangeable.
4. Expensive analysis is mode-gated; the meaning of an accepted safe program is not.
5. Build on existing effect inference. Earlier observations limited to the copy-budget verifier understated the source already present.
6. The collection/CUDA implementation work remains owned by its separate workstream. This report adds semantic tooling to refactor real callers, not an API-normalization adapter layer.

The inherited safe-code and warning-to-error policy is a dependency of this report, not redefined here. In particular, a warning-stage build is not a completed safety certification.

## Contents

1. Goals and the precise comparison with Rust
2. Source findings and reuse boundaries
3. One `unit` keyword: syntax and semantics
4. Shared type representation, layout, and parser cost
5. Invariants and contracts without expensive normal builds
6. Inferred effects: harden what already exists
7. Typed send/receive, resource state, and session protocols
8. Revocable capabilities: bounded adoption
9. Build modes, resource analysis, MIR, and FFI/ABI
10. LSP, CLI, and MCP additions
11. Refactoring and migration sequence
12. Acceptance tests and performance gates
13. Research decisions
14. Glossary
15. Delivery checklist and source index

## 1. Goals and the precise comparison with Rust

The goal is **stronger built-in guarantees for selected bug classes with less user ceremony**, not an unsupported claim that Simple currently dominates Rust's type system or implementation maturity.

Rust already supports nominal wrapper types, ownership, generic typestate, and libraries for units and session types. Its standard safety boundary does not establish absence of deadlock, resource leaks, or all logic errors; some safe logic errors can panic. [R1] Simple should build on these ideas while making selected checks and editor assistance systematic.

| Property | Baseline Rust capability | Target Simple improvement | Evidence required before claiming success |
|---|---|---|---|
| Semantic IDs and quantities | Newtype/library patterns | One `unit` surface, integrated dimension and nominal-identity diagnostics | Compile-fail tests for accidental mixing; representation tests |
| Value restrictions | Specific library types or custom validated wrappers; external refinement verifiers | Existing invariants feed construction, mutation, and local refinement checking | No unchecked construction or mutation escape |
| Allocation/I/O/blocking effects | Not a general built-in inferred function-effect row for all these properties | Complete, conservative summaries from current effect machinery; useful LSP explanations | Tests through closures, dispatch, cleanup, FFI, and generated code |
| Local resource lifecycle | Generic typestate patterns | Standard-library endpoints encode legal local transitions | Moves/borrows prevent stale aliases and forged state |
| Protocol order | Libraries such as Ferrite | Optional reusable protocol types, with short ordinary calls | Payload, direction, continuation, branch, and cancellation tests |
| Logical/container invariants | Not universally guaranteed by safe Rust | Cheap supported checks by default, deeper verification in analysis modes | Explicit distinction between proved facts and diagnostic assertions |
| Semantic migration tooling | Strong existing editor ecosystem | Unified unit/effect/state-aware AST query, change, and error-fix providers | Versioned, validated edits shared by LSP/CLI/MCP |
| Panic prevention | Baseline policy already covered in the earlier report | Preserve that policy when introducing units, effects, and states | No new hidden panic/trap paths in constructors or transitions |

Do not advertise universal termination, deadlock freedom, distributed agreement, or immunity to device failure. A claim beyond the supported subset requires its own proof and execution assumptions.

### 1.1 Required design properties

| ID | Requirement |
|---|---|
| ST-01 | `unit` is the sole final keyword for the four merged declaration roles. |
| ST-02 | Ordinary source remains short; existing punctuation, generics, attributes, and invariant blocks are reused. |
| ST-03 | Nominal identity, dimensions, representation, predicates, and protocol permissions remain separate compiler facts. |
| ST-04 | Normal builds invoke no heavyweight solver or whole-program protocol/model checker automatically. |
| ST-05 | High-overhead verification and instrumentation are allowed only in `debug`, `invest`, and `ci`, with explicit budgets. |
| ST-06 | A required property cannot become an unchecked assumption when deep checking is off. |
| ST-07 | Existing contract, effect, MIR, layout, and edit engines are extended, not duplicated. |
| ST-08 | Typed endpoints bind payload types to resources and enforce local state transitions using ownership. |
| ST-09 | Runtime checks for actual I/O, concurrent closure, FFI input, and cancellation remain where necessary. |
| ST-10 | LSP, CLI, and MCP share summaries, diagnostic identifiers, queries, and edit plans. |
| ST-11 | All examples below are proposed canonical syntax or API sketches unless explicitly marked observed. |

## 2. Source findings and reuse boundaries

These findings come from reading selected files at the pinned revision. They are not executed tests or an exhaustive repository audit.

| Source owner / file | Observed behavior | Consequence for this plan |
|---|---|---|
| `README.md`, unit examples | Measurement families use `unit length(base: f64):`; nominal suffix wrappers use `newunit UserId: i64 as uid`. | Preserve measurement-family behavior and migrate nominal declarations into the same keyword. |
| `src/compiler/30.types/custom_primitive_info.spl` | Custom-primitive metadata, primitive ABI names, and a flat 16-slot registry. Alignment is derived from primitive byte size in this helper. | Reuse conceptual metadata, but replace fixed limits and use the target layout authority. Do not infer ABI alignment from size alone. |
| `src/compiler/30.types/type_infer/inference_effects.spl` | HIR function effects, expression/block inference, row merging, effect compatibility, and caller accumulation exist. | Unify and harden existing machinery; do not start a second effect system. |
| Same effect inference file | Unhandled expression kinds return an empty list; failed direct-callee synthesis contributes no callee effects; unresolved methods fall back to IO only. | Empty and unknown must be distinct. IO-only fallback is not a complete upper bound for allocation, blocking, or other effects. |
| Same effect inference file | Lambda expressions collect body effects; array/dictionary literal cases only collect child effects locally. | Separate closure creation from invocation; audit allocation introduced by lowering. These observations do not prove no other pass compensates. |
| `src/compiler/35.semantics/effect_verifier.spl` | Copy-budget and bounded-loop checks, with direct-call cost propagation and documented gaps. | Integrate summaries; do not use a lower-bound cost estimate as proof of an upper-bound guarantee. |
| `src/app/interpreter/core/contract.spl` | Entry/exit contract checking, invariants, and `old()` capture helpers already exist. | Improve placement, capture cost, and compiler/interpreter parity. |
| `src/compiler/20.hir/hir_lowering/_Items/verification_contract_lowering.spl` | Existing contract lowering, including normal/error postconditions. | Reuse contract AST/HIR and predicate validation. Presence is not proof of full object-invariant enforcement. |
| `src/lib/nogc_sync_mut/concurrent/channel.spl` | `Channel` stores an integer handle; `send<T>` and `recv<T>` are independently generic methods; `send` discards admission status. | Introduce payload-typed endpoints; make rejected sends observable. Verify negative examples before asserting a runtime defect. |
| `src/lib/nogc_async_mut/concurrent/channel.spl` | Re-exports the synchronous channel owner in the inspected tree. | Audit actual blocking/suspension behavior; an async namespace is not an effect proof. |
| `src/lib/nogc_sync_mut/tcp/{types,send,receive}.spl` | Integer state constants and runtime state tests; invalid send returns unchanged data and invalid receive returns empty text. Receive-buffer helper is explicitly a simulation. | Runtime state machines already exist, but these APIs do not encode static lifecycle state. Do not mistake simulated buffers for a verified network backend. |
| `src/compiler_rust/lib/std/src/async/sffi/channel.spl` and legacy TCP files | Additional scalar-handle channel/TCP paths. | Include legacy/bootstrap paths in migration and ABI tests; they are not the only current owners. |
| `src/compiler/50.mir/mir_verify.spl`, `mir_verify_levels.spl` | Lightweight structural verification and severity machinery exist. | Extend this verifier; gate only expensive verification, not mandatory structural/type checks. |
| `src/compiler/20.hir/abi_interface.spl` | Canonical interface summaries/hashes. | Extend with relevant type/effect/state commitments; signature hashing alone does not verify foreign behavior. |

Before implementation, resolve current paths and production call sites. An existing helper, test fixture, comment, or parser branch must not be reported as end-to-end support without driver and backend evidence.

## 3. One `unit` keyword: syntax and semantics

### 3.1 The merger

The four merged roles are measurement units, nominal semantic IDs (formerly `newunit`), nominal custom wrappers (formerly `newtype`), and refinement-constrained values. A constrained value is a nominal/custom declaration plus a predicate, not a fourth independent runtime representation.

| Role | Proposed canonical form | Meaning |
|---|---|---|
| Nominal ID | `unit UserId: u32 as uid` | Distinct identity; optional literal suffix |
| General nominal wrapper | `unit PacketSize: u32` | Distinct type over an existing representation |
| Constrained value | `unit Port: u16:` followed by an existing invariant block | Nominal value plus validity condition |
| Measurement family | `unit length(base: f64):` with scale definitions | Physical dimension and named scales |
| Derived measurement | `unit velocity(base: f64) = length / time:` | Dimension expression plus scales |
| State marker | `unit Ready` | Nominal, zero-payload type for a generic state parameter |
| Transparent alias | `unit ByteCountAlias = ByteCount` | Another spelling of the same type, not a new identity |

The alias form keeps an important distinction explicit: **colon introduces a nominal wrapper; equals introduces an alias**. The `(base: ...)` header identifies a dimension declaration, so its equals expression is a dimension expression. Existing unrelated `type` aliases need not be mass-migrated in this work; if migrated, preserve alias semantics exactly.

No new `refined`, `newstate`, `session`, `newunit`, or `newtype` keyword is required. Ordinary `class`, `struct`, `enum`, and function declarations are unaffected.

### 3.2 Proposed examples

```simple
# Nominal types: these are not interchangeable merely because both use u32.
unit UserId: u32 as uid
unit OrderId: u32 as oid

val user: UserId = 42_uid
val order: OrderId = 42_oid
# val wrong: UserId = order        # type error

# A validity predicate uses the existing contract/invariant mechanism.
unit Port: u16:
    invariant:
        value > 0

# Existing measurement-family form is retained.
unit length(base: f64):
    mm = 0.001, cm = 0.01, m = 1.0, km = 1000.0

unit time(base: f64):
    ms = 0.001, s = 1.0, min = 60.0

unit velocity(base: f64) = length / time:
    mps = 1.0

val distance = 2_km
val duration = 10_s
val speed = distance / duration
# val bad = distance + duration    # dimension error

unit Open
unit Closed
unit ByteCount: u64
unit CountAlias = ByteCount
```

The scalar predicate binding `value` and attachment of an invariant block to `unit` are part of this proposed canonicalization. Validate them against the existing parser and binding rules; do not advertise the example as already accepted by every engine.

For a constrained type, the API distinguishes statically justified construction from dynamic validation:

```simple
val port = Port(8080)              # accepted when the predicate is proven
val dynamic_port = Port.try_from(raw)?  # Result<Port, ValidationError>
```

An unknown value cannot enter the refined type by an unchecked constructor. A checked constructor may return an error even for a statically known invalid value; it remains a valid total operation.

### 3.3 Semantic rules that the merger must preserve

1. **Nominality:** `UserId` and `OrderId` remain different despite identical representation.
2. **Aliases:** an alias resolves to its target identity. A syntax migration must not change overload, trait, equality, or serialization behavior.
3. **Dimensions:** equivalent normalized measurement expressions can interoperate under the defined conversion rules; unrelated nominal wrappers do not become interchangeable.
4. **Predicates:** refinements compose with the base type's validity rules. They cannot be dropped by casts, FFI import, deserialization, reflection, generated code, or assignment.
5. **Operations:** do not derive every primitive operator automatically. Adding two IDs is not inherently meaningful; a nonzero value is not closed under subtraction.
6. **Results:** an operation returning the same refined type must prove closure or return a checked result. It may instead return an explicitly documented wider type.
7. **State:** representation equality never permits casting `Handle<Closed>` to `Handle<Open>`. Resource construction and transitions are controlled by their owner.
8. **Suffixes:** `as uid` declares a literal suffix; it does not grant unchecked conversion or erase nominal identity.

Operator capabilities and arithmetic policies reuse existing traits/attributes. Migration preserves supported old operations or emits an actionable diagnostic; it must not silently broaden operators to make old code compile.

### 3.4 Conversion rules

- Normalize dimensions and exact scale ratios in compiler metadata, not by repeatedly manipulating text.
- Constant conversions can fold at compile time. A runtime scale conversion can still require multiplication/division; type erasure does not erase necessary arithmetic.
- Integer narrowing, inexact conversion, range overflow, and floating-point validity use explicit checked or documented conversion semantics.
- Do not treat affine quantities such as absolute temperatures as ordinary multiplicative dimensions. Separate points from differences, or require explicit conversion APIs.
- Nominal concepts with the same physical dimension may intentionally remain distinct. Torque and energy, for example, need not be interchangeable in a domain API.
- Currency, device clocks, epochs, and addresses require explicit contextual conversion; a shared numeric representation is insufficient.

## 4. Shared type representation, layout, and parser cost

### 4.1 One canonical type description, separate facts

Extend the existing type interner/metadata rather than adding a parallel `NominalType` registry. Conceptual fields:

```text
UnitTypeInfo
    declaration_id
    identity_kind              # nominal, alias, dimension family, marker
    underlying_type_id
    predicate_set_id           # optional; interned
    dimension_expression_id    # optional; normalized
    scale_table_id             # optional
    operator_capabilities
    literal_suffixes
    source_origin
```

Keep target-independent facts immutable in shared HIR. Target layout, calling convention, selected backend effects, and code generation belong in the concrete MIR/target overlay. Do not put host-dependent alignment or endian assumptions into reusable HIR.

Use compact IDs and side tables for uncommon metadata. Do not allocate a large map for every AST node or carry type-name strings in generated values. A full canonical definition is authoritative; hashes accelerate lookup and are not a substitute for identity validation.

The inspected 16-entry custom-primitive helper cannot be the final global registry. Reuse the scalable type interner, and derive ABI size/alignment from the existing target layout engine. A primitive with eight-byte storage does not universally require eight-byte ABI alignment.

### 4.2 Representation promises

| Case | Intended representation | Qualification |
|---|---|---|
| Primitive-backed nominal value | Underlying scalar where transparent layout is valid | No per-value nominal tag; target ABI must be tested |
| Refined scalar | Same scalar | Construction/mutation must enforce validity |
| Measurement value | Underlying numeric representation | Conversion arithmetic remains when needed |
| State marker | No stored marker payload | Does not eliminate the underlying resource handle |
| Static protocol endpoint | Transport handle plus any real transport data | Do not add a protocol tag solely for statically known local state |
| Dynamically selected state/branch | Existing sum/enum representation if required | Genuine runtime uncertainty may require a discriminant |
| Reflected/dynamic values | Existing dynamic-value representation | Do not promise removal of tags needed by the interpreter |

Reuse the earlier optional/niche layout rules; this merger neither creates spare bits in a full-range primitive nor permits an invalid primitive value in a nonoptional type.

### 4.3 Parser and GPU parser design

This requires a **small grammar refactor**, not zero grammar work. It adds no new keyword or punctuation.

After `unit Name` and optional existing generic parameters:

| Next token | Parse as |
|---|---|
| `:` | Underlying type, optional suffix, optional declaration body |
| `(` with the existing `base:` header | Measurement family or derived measurement |
| `=` | Transparent alias |
| End of declaration | Zero-payload marker |

Retain the current generic/type/expression subparsers. The parser need not resolve dimensions, prove a predicate, infer effects, or analyze typestate. Those are semantic passes.

CPU, SIMD, GPU, tree-sitter, formatter, and LSP parsers must share the same grammar version and golden cases. Validate lookahead and conflicts with actual parser tests; do not claim LL(1) merely from a sketch. No GPU-specific refinement solver or state checker is proposed.

### 4.4 Glossary/tooling consequences

Use one public term, **unit declaration**, then explain its semantic role in hover/documentation: nominal ID, measurement family, refined value, alias, or state marker. Preserve old keywords as migration search terms only. The IDE must not describe every `unit` as a physical measurement.

## 5. Invariants and contracts without expensive normal builds

### 5.1 Reuse, do not replace

Reuse existing contract AST/HIR, interpreter entry/exit helpers, normal/error postconditions, and `old()` support. Add ownership-aware placement and proof classification.

| Classification | Normal/release handling | Analysis-mode addition |
|---|---|---|
| Simple, statically proved predicate | Retain proof fact; erase redundant runtime check | Optional cross-check instrumentation |
| Cheap dynamic boundary validation | Check once; return typed failure; construct valid value only after success | Trace failures and provenance |
| Method known to preserve an invariant | Reuse verified summary plus caller checks | Reverify method body/dependencies |
| Expensive diagnostic assertion | Do not assume it as a type fact when disabled | Execute or prove with explicit budget |
| Expensive predicate required for type validity | Use an invariant-preserving constructor, valid proof evidence, or reject unproved construction | Deep proof or diagnostic validation |

**Critical distinction:** a predicate omitted from release cannot justify optimization, a niche, an unchecked load, or a state transition unless it was independently established. Debug-only checks are not release proofs.

If establishing a required predicate on arbitrary external input inherently requires an expensive scan, this policy does not make that cost disappear. Use a verified incremental ingestion algorithm, an appropriate certified boundary, or a less-refined input API. Do not expose an unvalidated refined value in normal mode.

### 5.2 Reduce recurring invariant cost

1. Prove construction and invariant-preserving mutators once per definition/instantiation summary.
2. Check externally observable boundaries, not every private helper step.
3. Track which fields and aliases a mutation affects; invalidate only dependent facts.
4. Preserve invariants on normal return, typed-error return, cleanup, and cancellation. Temporary internal invalidity must not escape through callbacks, suspension, or reentrancy.
5. Treat `await`, unknown foreign calls, and shared mutation as fact-invalidation points unless the relevant ownership/locking evidence prevents interference.
6. Capture only the `old()` fields actually referenced by remaining checks. Erase unused captures; avoid general dictionary/string snapshots in a hot path.
7. For collection invariants, prefer operations that preserve the property locally over rescanning the entire collection after each update.
8. A runtime predicate must itself be total and have bounded, permitted effects. Avoid validating safety using a predicate that can panic, allocate unexpectedly, or perform I/O.

Example: for a bounded queue, checking a local size update against capacity is cheap. Proving that an arbitrary user mutation preserved sortedness may be expensive; normal compilation must not assume the full-array property just because CI did not report a counterexample.

### 5.3 Proof reuse

If deep verification produces reusable evidence, bind it to the exact normalized semantic body, referenced summaries, predicate definitions, verification-policy/version, compiler/IR schema, and relevant target assumptions. Preserve source-map provenance for explanations; a comment-only change need not invalidate a semantic proof if the canonicalization rule itself is versioned and checked. Ordinary builds may validate an admitted certificate or trusted proof artifact without rerunning a solver. A Boolean `verified=true`, a test pass, or a content hash alone is not a proof.

Changed dependencies invalidate evidence. A timeout, unsupported case, stale cache, or missing backend model is `unknown`, never success. Keep this evidence path optional initially: ordinary cheap checking and safe checked APIs must work without a proof service.

## 6. Inferred effects: harden what already exists

### 6.1 Meaning and source of facts

An effect describes possible behavior, not a measured event count. Start from existing `EffectKind` definitions and normalize their meanings; do not add a competing taxonomy.

Examples of normalized facts are allocation, I/O, mutation, suspension, blocking, device access, and the inherited safety failure effects. Map existing `Allocates`, `IO`, `Async`, `Mutates`, `Throws`, and custom effects through one registry.

`async` means a computation may suspend according to its execution model; it does not prove nonblocking. `nogc` does not prove no allocation. A typed-error return does not prove absence of panic. Local mutation, externally observable mutation, and purity require an explicit policy, not a name-based guess.

I/O is identified from the **resolved operation**:

- Compiler/runtime intrinsics have audited summaries.
- Simple function bodies propagate their callees' summaries.
- FFI functions use checked binding metadata.
- Dynamic dispatch uses effect bounds attached to the callable interface.
- Unknown implementations remain unknown.

`socket.send` may perform network I/O; a queue's `send` may only synchronize shared memory; a simulated TCP buffer helper may only allocate/mutate memory. Identical method names are not evidence of identical effects.

### 6.2 Repair concrete gaps

| Observed or required gap | Required change |
|---|---|
| Unhandled HIR kind returns `[]` | Track unknown/unmodeled behavior; require exhaustive effect coverage tests |
| Failed callee-type synthesis contributes nothing | Preserve the type error and mark effect summary incomplete |
| Unknown method becomes IO only | Use an unknown/top summary, not a fabricated exhaustive IO summary |
| Closure body effects attributed to creating the closure | Separate capture/creation effects from latent invocation effects |
| Literals only merge child effects | Account for actual lowered allocation or verified storage-free lowering |
| `Throws` comparison ignores payload type in inspected helper | Preserve typed-error identity or a sound upper bound |
| Copy-budget propagation only sees direct calls | Keep completeness metadata; never label a lower bound as an upper-bound proof |
| Generated operations/cleanup omitted | Include implicit conversion, drop, formatting, serialization, AOP, and callback effects |
| Host backend changes behavior | Keep common HIR facts and target-specific MIR effect refinement |

An unknown effect does not make every unrestricted function illegal. It prevents unsupported promises such as no-allocation/nonblocking/panic-free where those guarantees are required.

### 6.3 Low-cost implementation

Use a compact bitset for a fixed set of coarse may-effects and interned side records for error types, callback effect parameters, and affected regions. Keep completeness/provenance separate from the mask.

```text
FunctionSummary
    may_effects
    completeness
    callback_effect_parameters
    state_transition_summary_id
    invariant_summary_id
    dependency_fingerprint
    target_scope
```

The union of known callees' effects is cheap. A worklist over the call graph reaches a fixed point for a finite bitset; use SCCs for recursion and incremental invalidation. This is not a claim that all effect analysis is a single OR instruction: call resolution, higher-order bounds, and unsupported features still need work.

For higher-order functions, propagate the callback's declared/inferred effect bound. Do not run an expensive global points-to analysis in normal builds. If that bound is absent, retain unknown effects; `invest`/CI may improve precision but cannot retroactively legalize an unchecked ordinary call.

Resource identity and state transitions are not bits such as `CLOSED` on a whole function. They are separate, resource-specific ownership facts.

### 6.4 Cache and LSP connection

Publish semantic summaries through existing TLDR/immutable cache facilities. Keep usage/reference edges in the existing reverse-reference mechanism rather than changing a public summary for every newly discovered caller. Invalidate callers when an exported effect/state/predicate summary changes.

LSP consumes these compiler facts; it does not independently infer I/O from names or documentation. It must show `complete`, `incomplete`, `stale`, and `target-dependent` distinctly. Cold misses return pending/unknown promptly, not a false purity badge.

## 7. Typed send/receive, resource state, and session protocols

### 7.1 Three independent improvements

Do not call a channel state-typed merely because it has a state integer or a generic message method.

| Level | What becomes impossible | Implementation |
|---|---|---|
| Payload type | Sending one type and receiving an unrelated type through the same typed endpoint | `Sender<T>`, `Receiver<T>`, or equivalent resource-bound `Channel<T>` |
| Local lifecycle | Using a locally consumed/closed handle; invalid local half-close transitions | Ownership plus state parameters/permissions |
| Session protocol | Sending/receiving the wrong message or using the wrong direction at the current protocol step | Optional generic continuation types |

Implement payload typing first. A separate `T` chosen at each `send<T>` and `recv<T>` call is not, by itself, a payload-type relationship between endpoints.

### 7.2 Ordinary shared channels

Use a single payload type attached at creation:

```simple
# Proposed API; no new language constructs.
val (tx, rx) = channel<Request>(capacity)?
tx.send(request)?
val request = rx.recv()?
```

Required semantics:

- A sender and receiver created together share the same payload type and transfer policy.
- A send reports admission failure. Do not silently discard a message because a runtime status was ignored.
- Where a rejected message was not transferred, return ownership in a typed error. Do not return a second owned copy after a partially committed transfer.
- A nonblocking empty result, a drained closed channel, cancellation, and timeout have documented, distinguishable meanings.
- Preserve draining of buffered messages after closure. Global channel closure does not imply that a receive immediately has no message.
- Creation can fail through the existing typed allocation/resource error policy.
- Unsafe scalar-handle import is not a public way to forge arbitrary `Channel<T>`. A safe imported handle needs payload, ownership, lifetime, and runtime registration evidence.

An MPMC queue can be closed by another thread. Its actual open/closed/full state still requires synchronization and runtime checks. A local `Sender<T, Open>` marker, if used, means that the caller has not consumed its endpoint; it cannot prove the global queue remains open.

Do not force arbitrary MPMC traffic into a single linear conversation protocol. Ordinary work queues remain simple.

### 7.3 TCP local lifecycle and half-close

Prefer direct construction of a usable resource over requiring a dummy disconnected object:

```simple
unit ReadOpen
unit ReadShut
unit WriteOpen
unit WriteShut

# Conceptual signatures; ownership and async spelling reuse existing syntax.
fn connect(addr: SocketAddr) -> Result<TcpStream<ReadOpen, WriteOpen>, IoError>
fn send(s: &mut TcpStream<ReadOpen, WriteOpen>, data: bytes) -> Result<usize, IoError>
fn receive_into(s: &mut TcpStream<ReadOpen, WriteOpen>, dst: &mut bytes) -> Result<usize, IoError>
fn shutdown_write(s: TcpStream<ReadOpen, WriteOpen>) -> Result<TcpStream<ReadOpen, WriteShut>, ShutdownError>
fn close(s: TcpStream<ReadOpen, WriteOpen>) -> Result<(), CloseError>
```

These are explanatory sketches, not a mandate to duplicate implementations for every state combination. Generalize send over states with write permission and receive over states with read permission using existing trait/generic machinery. Close is available for the remaining owned lifecycle states.

```simple
val connected = TcpStream.connect(addr)?
val read_only = connected.shutdown_write()?
val n = read_only.receive_into(buffer)?
# read_only.send(data)             # compile error: local write permission removed
read_only.close()?
# read_only.receive_into(buffer)   # compile error: endpoint consumed
```

Use distinct bindings in examples and migration unless type-changing reassignment is explicitly supported. A type merger does not implicitly introduce variable retyping.

Additional requirements:

1. State parameters are semantically meaningful even when erased from layout. Preserve ownership, lifetime, variance, and transfer constraints.
2. State-changing methods consume or exclusively borrow the right resource. Constructors are sealed where necessary; cloning and representation casts cannot recreate a consumed capability.
3. A normal `close` need not return a `Closed` object. Consuming the resource and returning a typed outcome is often simpler.
4. Each failed/partial transition defines who owns the handle and which operations remain permitted. Do not automatically revive `Open` after a failed close.
5. If the backend cannot establish a precise post-state, retain an explicit uncertain/cleanup-only continuation or transfer cleanup responsibility to the runtime. Bind this to actual OS semantics.
6. Read/write calls can still fail, return EOF, or complete partially. Typestate describes legal local API use, not the remote peer or kernel's future state.
7. Do not expose the entire TCP wire-state machine as permanent user type parameters. Handshake/FIN/timer state remains the transport's runtime responsibility.

### 7.4 Optional session-typed channels

Provide ordinary library types for protocol continuation, not a new protocol DSL:

```simple
unit End
unit ClientProtocol = Send<Request, Recv<Response, End>>
unit ServerProtocol = Recv<Request, Send<Response, End>>
```

The protocol types are generic descriptors, not extra runtime messages. Their semantic operations are:

```text
Endpoint<Send<T, Next>> --send T--> Endpoint<Next>
Endpoint<Recv<T, Next>> --receive--> (T, Endpoint<Next>)
Endpoint<End>          --finish--> completed endpoint
```

This notation describes type transitions; it is not new Simple grammar.

```simple
# Proposed library usage with inferred intermediate endpoint types.
val client = connect_session<ClientProtocol>(addr)?
val awaiting_reply = client.send(request)?
val (response, finished) = awaiting_reply.recv()?
finished.finish()?
```

Required rules:

- Consuming a protocol endpoint makes the previous continuation unusable.
- Both endpoints agree on dual message directions and payload types.
- Branching uses existing sum types and exhaustive matching; unselected alternatives do not remain usable.
- Repetition uses a finite named protocol graph, not infinite generic expansion.
- Session endpoints are not freely copyable. Shared access needs an explicit serialized ownership/acquisition protocol.
- Protocol descriptors alone do not establish liveness or deadlock freedom. Any stronger session-theoretic guarantee must state and enforce its assumptions.
- Typed local protocols do not validate an arbitrary network peer. Framing, payload validation, protocol version negotiation, and authentication remain boundary work.

Ferrite demonstrates this library-level continuation style, including `SendValue`, `ReceiveValue`, and `End`; Simple can reuse the idea without copying Ferrite's proof-oriented surface. [R5]

### 7.5 Async cancellation and commit points

For every async send/receive/transition, specify:

| Outcome | Required ownership/state result |
|---|---|
| Successful completion | Produce the documented next endpoint state |
| Rejected before transfer commits | Return the original permitted continuation and message when safe |
| Partial transfer / uncertain delivery | Do not assume retry is harmless; expose typed uncertain outcome or terminal cleanup |
| Cancellation before commit | Preserve or return original state only when the backend guarantees this |
| Cancellation after commit | Preserve the committed next state or terminate safely; never replay automatically |
| Task destruction | Release resources and pending operations according to a defined cleanup contract |

This is required design work, not an optional debug check. Expensive exploration of schedules belongs in `invest`/CI; ordinary state and ownership rules remain enforced.

### 7.6 Migration owners

Update current channel owners and all re-exporting runtime variants, then TCP/resource wrappers and the relevant SOSIX boundary. Check bootstrap/legacy `compiler_rust` signatures as compatibility consumers.

Do not replace working transport code with the inspected tuple-buffer simulation. First identify the real backend call graph. The planned typed wrapper must describe actual resource behavior, not merely a model used in examples.

## 8. Revocable capabilities: bounded adoption

The PLDI 2026 paper *Typestate via Revocable Capabilities* explores permission revocation when resource state changes, including aliased resources and session APIs. It is a design reference, not evidence that Simple can obtain the same guarantees from generics alone. [R6]

### 8.1 Adopt the narrow, useful subset

1. Use existing ownership/borrowing for unique resources and short-lived views.
2. Record which resource identity and state justify each derived permission.
3. A local transition either requires all incompatible borrows to end or invalidates their use in a sound flow-sensitive model.
4. Closures, fields, captures, and returned values must retain permission dependencies.
5. At control-flow joins, only facts true on all reachable paths remain available.
6. Across suspension or unknown calls, invalidate facts that interference could break.

For the common "reader still borrowed when owner closes" example, ordinary borrowing may be sufficient. Do not build a second ownership system for that case.

### 8.2 Do not import research prototype gaps

The published artifact documents incomplete handling of mutable variables/object fields and restrictions involving polymorphic values. Some unsupported revocations do not take effect in that prototype. Simple must reject or conservatively downgrade unsupported cases; it must not reproduce silent acceptance. [R7]

Advanced shared capabilities, higher-order revocation, and multiparty session verification are later work. They require a defined soundness model and concrete demand. Deep analysis can be mode-gated, but a program that relies on a capability guarantee must still satisfy an enforceable ordinary-build rule or admitted proof.

Static revocation cannot notify arbitrary foreign code or a remote peer. Do not describe it as a replacement for runtime locks, atomics, generation checks, or OS handle validation when those are necessary.

## 9. Build modes, resource analysis, MIR, and FFI/ABI

### 9.1 Final mode policy

`invest` is the canonical name used here for investigation/inspection mode. It is build configuration, not a language keyword. Reuse the existing build configuration mechanism; any `inspection` alias maps to the same mode.

| Check / work | Normal and release | Debug | Invest | CI |
|---|---|---|---|---|
| Name/type checking, units/dimensions | Required | Required | Required | Required |
| Supported ownership and state rules | Required | Required | Required | Required |
| Cheap effect summaries and required bounds | Required | Required | Required | Required |
| Lightweight structural MIR verification | Required | Required | Required | Required |
| Necessary typed boundary validation | Required | Required | Required | Required |
| Deep invariant/refinement solvers | Off | Explicit/budgeted | Selected functions + dependency closure | Configured changed/full scope |
| Whole-program alias/protocol/model analysis | Off | Explicit/budgeted | Selected investigation | Configured comprehensive checks |
| Expensive invariant instrumentation | Off | Opt-in | Selective | Test binaries |
| Expensive XRay/profile/resource tracing | Off | Opt-in | Selective | Benchmark/test jobs |
| Expensive MIR pass-by-pass/translation validation | Off | Optional | Selected transforms | Compiler validation jobs |
| Solver/trace caches | Read only admitted lightweight evidence if needed | Separate analysis namespace | Separate analysis namespace | Produce validated evidence |

High-overhead analysis is **allowed only** in the three analysis modes; it need not run on every debug compilation. Reuse cached summaries and explicit budgets so debug remains usable.

Normal mode must never automatically launch a solver because a small check failed. Its outcomes are: accept with sufficient evidence, use a specified checked API, or diagnose an unproved required property.

### 9.2 What remains cheap and mandatory

- Nominal identity and dimension matching.
- Const folding, interval facts, bounded local flow analysis, and pattern exhaustiveness.
- Existing borrow/move rules and supported endpoint-state transitions.
- Conservative effect upper bounds and unknown propagation.
- Checking declared signature/layout compatibility at module/link/load boundaries.
- MIR type/operand/control-flow validity at defined handoff points.

Avoid promising all such checks are constant time. Their work scales with the affected code and metadata, but they require no heavyweight proof search.

### 9.3 Resource guarantees versus resource diagnostics

Use the existing `@copy_budget`, `@bounded_loop`, no-allocation machinery, and pool/resource helpers where applicable.

| Property | Cheap default support | Deep mode work | Limitation |
|---|---|---|---|
| No heap allocation on a path | Effect summary and audited callee bounds | Hidden allocation audit/profiling | Profiling alone cannot prove all executions |
| Fixed-capacity pool use | Type/capacity checks and typed exhaustion | Capacity stress and workload analysis | External load still may exhaust a pool |
| Bounded copies | Sound upper-bound summaries | Layout/backend and all-dispatch audit | Lower-bound counting is not proof |
| Stack / recursion bounds | Enforced local restrictions where a profile requires them | Recursion/resource proof | Must not ignore known fatal paths |
| Lock discipline | Supported lock rank/ownership constraints | Schedule/model exploration | No universal deadlock-free claim |
| Latency/WCET | Explicit deadlines and typed timeouts | Target-specific analysis and measurements | Hardware/system assumptions are required |

Disabling resource diagnostics does not waive a resource bound that a function's safety contract depends on. If the needed bound is unavailable, reject the claim or use a fallible operation.

### 9.4 MIR verification placement

Keep the existing lightweight verifier at IR handoff/cache/backend boundaries and extend it with representation/state-summary consistency. Do not add a heavyweight checker after every optimization in ordinary builds.

Expensive translation validation, solver-backed invariants, GPU race/barrier exploration, and proof of optimizer transformations run only in the analysis modes. Their results must be tied to actual production IR and selected backend rules, not a separate toy AST.

For instrumentation/AOP, re-evaluate the artifact's effects after transformation. A source function's no-allocation summary is not proof that an instrumented executable never allocates. Keep base and instrumented artifact guarantees distinct; no generated layer may silently violate required safety.

### 9.5 FFI/ABI and device boundaries

1. Keep target-independent signatures/types in HIR and target layout/calling conventions in the MIR overlay.
2. Check real symbol mappings, parameter/result representation, calling convention, ownership, nullability, and callback effects.
3. Unit erasure may preserve scalar layout, but it does not validate a foreign integer as a port, a handle as live, or a pointer as uniquely owned.
4. Encode semantic unit/predicate/protocol commitments in interface metadata without automatically changing the physical ABI.
5. Validate refinements when crossing an untrusted/untyped boundary. On success, construct the typed value; on failure, return an ordinary error.
6. Unknown foreign effects cannot prove no-allocation/nonblocking/panic-free obligations. Use an audited wrapper or explicit trusted boundary with recorded scope.
7. Dynamic modules and hot replacement must satisfy the same effect/state ABI commitments at admission. A plugin cannot silently strengthen preconditions or weaken guarantees.
8. Deep cross-language analysis belongs in `invest`/CI, while inexpensive boundary checks and admission remain in normal builds.
9. CPU, CUDA, Vulkan, and foreign serializers must preserve semantic type/payload information even when device memory contains only primitive data.

### 9.6 Cost summary

These are design expectations, not measured Simple results.

| Feature | Normal compile cost | Normal native runtime cost | Interpreter consideration | Grammar impact |
|---|---|---|---|---|
| Unified nominal/alias resolution | Interner lookups | No extra nominal tag | Reuse existing value/type representation | Consolidated declaration forms |
| Dimension normalization | Small compile-time algebra; cache results | Only real conversion arithmetic | Cache normalized metadata | Existing dimension syntax |
| Scalar refinements | Cheap local facts | Necessary boundary comparison unless proved | Validate once, not every read | Reused invariant body |
| Effect propagation | Incremental graph work | No effect dispatch/bitset per call | Analyze once per compiled/loaded chunk | None |
| Payload-typed endpoints | Generic/type checks | Transport work unchanged | Retain boundary validation | None |
| Erased static typestate | Ownership/state checks | No new state marker field | Existing handle representation remains | Marker `unit` form |
| Optional sessions | Generic graph checks; cap expansion | No marker cost; real branch/wire handling remains | Cache transition descriptors | Existing generics/sums |
| Deep proofs/model checks | Off | Off | Off | None |
| LSP facts | Lazy queries over caches | Not part of application runtime | Not applicable | No effect |

Control generic code-size growth. Intern equivalent protocol graphs, cap recursive expansion, and share generated bodies when representation and semantics genuinely permit it. Erasing a marker never permits erasing lifetime/ownership constraints.

## 10. LSP, CLI, and MCP additions

### 10.1 Reuse the earlier semantic edit core

Add providers and query facets to the existing/shared AST/CST semantic service. Do not introduce an independent LSP writer, an agent-specific regex rewriter, or a second error-fix engine.

The compiler is authoritative for resolved types/effects/states; the CST supplies precise source ranges, comments, and formatting. Edits are produced as versioned plans through the shared transaction/validation system.

### 10.2 New visible features

| Feature | What the user/agent sees | Required semantic source |
|---|---|---|
| Unit hover | Role, underlying representation, identity, suffix, dimension, predicate | Canonical unit/type metadata |
| Conversion explanation | Why two types differ; exact scale/overflow/inexactness consequences | Dimension/conversion resolver |
| Effect hover/inlay | Known may-effects, unknown effects, target, analysis completeness | Function summaries |
| Effect provenance | Which resolved callee/operation introduces allocation, I/O, blocking, or suspension | Dependency graph with source origins |
| Typestate hover | Current endpoint state, permitted operations, next states | Ownership/state flow |
| Alias explanation | Which live borrow/capture prevents a transition | Borrow/permission dependencies |
| Session progress | Required next message/direction and compatible branches | Protocol continuation graph |
| Invariant view | Proven / checked at boundary / unknown / diagnostic-only | Contract classification and evidence |
| Inspect action | Run budgeted deep analysis on selected code and dependencies | Analysis job service, not synchronous typing |
| Migration preview | Role-preserving unit conversion and caller/contract impact | Shared refactoring providers |

Keep live analysis cheap. Deep work is cancellable and starts only on an explicit analysis-mode action or configured CI job.

### 10.3 New AST search and change providers

Extend structural queries with fields such as:

```text
declaration.kind = nominal | measurement | alias | state_marker
declaration.has_refinement = true
declaration.has_dimensions = true
declaration.has_literal_suffix = true
function.effects.contains = alloc | io | block | suspend
function.effects.completeness = complete | unknown
function.state_transitions.any.action = consumes | preserves | produces
function.state_transitions.any.resource = <resource-parameter-id>
call.resolved_symbol = <symbol-id>
expression.refinement_status = proven | checked | unknown
```

These are conceptual query fields in the existing service, not language keywords.

Required helpers:

- Find all `newunit`/`newtype` declarations and the semantic role of each.
- Convert a declaration to canonical `unit` while preserving suffix, identity, representation, and comments.
- Find/correct mismatched units through resolved references, not name matching.
- Find functions with disallowed effects and provide the shortest justified cause chain.
- Find channel endpoints whose payload type is not bound at resource creation.
- Find calls that reuse a moved endpoint, violate a protocol step, or hold incompatible aliases.
- Update a function/method signature, callers, extension imports, and related contracts as one validated plan.
- Update generated source at its generator/template origin, not by permanently patching an expansion.

### 10.4 Error-fix policy

| Diagnostic | Offer | Do not do automatically |
|---|---|---|
| Deprecated `newunit`/`newtype` | Semantics-preserving conversion to `unit` | Turn an alias into a nominal type or change existing operators |
| Unit mismatch | Show explicit conversion candidates and their precision behavior | Erase type identity with unchecked casts |
| Invalid refined construction | Checked constructor, guard, or reuse of a validated value | Add an unproved invariant/assumption |
| Forbidden allocation | Caller-supplied buffer or a verified nonallocating overload when behavior matches | Remove the restriction to suppress the diagnostic |
| Wrong endpoint state | Show legal operations; suggest a verified local ownership refactor | Insert network sends, retries, closes, or reconnects without intent |
| Wrong protocol order | Show expected next action and conflicting call | Fabricate a missing message or silently drop a step |
| Unknown foreign effects | Locate missing binding metadata/audit | Invent a purity/no-allocation annotation |
| Incomplete proof | Run `invest`, retain checked path, or request explicit API redesign | Treat test success as proof |

Classify fixes as **mechanical**, **behavior-changing repair**, or **suggestion requiring evidence**. Only verified semantics-preserving fixes belong in unattended fix-all. Interface changes, error propagation, unit rounding, and protocol changes require preview and dependency impact.

Contract suggestions are optional documentation/domain aids. They never turn an unproved required property into a caller obligation silently, and do not make programmer-written `requires` mandatory.

### 10.5 Standard LSP and negotiated extensions

Use standard diagnostics, hover, inlay hints, symbols/references/rename, code actions, lazy `codeAction/resolve`, and versioned workspace edits. The official protocol site identifies 3.18 as current; negotiate actual client capabilities and retain a compatible subset for older clients. [R9]

AST search/manipulation, effect-path queries, unit migrations, session views, and inspection jobs are Simple-specific negotiated extensions or commands. They are not standard LSP methods.

A `WorkspaceEdit` is **not inherently atomic across multiple files**. Respect client failure-handling capabilities and the shared edit engine's validation/recovery protocol. Never announce success merely because the editor accepted a request. Unsaved buffers, stale diagnostics, concurrent agents, generated files, and mixed line endings remain protected by snapshot/version checks.

### 10.6 CLI/MCP parity

Proposed user-facing commands (reuse existing command routing; names are not claimed implemented):

```sh
simple inspect type src/net/client.spl --symbol Port
simple inspect effects src/net/client.spl --symbol send_request --why
simple inspect state src/net/client.spl --symbol request_reply
simple refactor unit --scope src --preview
simple fix --diagnostic ST-UNIT-LEGACY --preview
simple check --mode invest --scope src/net --budget-ms 5000
simple check --mode ci --report report.sdn
```

The CLI and MCP call the same operations and produce the same diagnostic/edit-plan identifiers as LSP. `--preview` is read-only. Applying a plan is an explicit separate operation and revalidates the snapshot.

Inspection output includes mode, target, covered dependency closure, unknown cases, proof provenance, and cost. The agent can request an AST subtree or exact text when necessary without losing semantic validation on the eventual edit.

### 10.7 Collection/CUDA workstream integration

Consume a migration description from the owning workstream: resolved old/new symbols, parameter mapping, ownership/effects, return types, extension import changes, and supported backends.

The semantic engine updates actual source references and arguments, preserves evaluation order, inserts temporaries where justified, and rechecks unit/payload/state obligations. It does not redesign the collection APIs, choose semantic conversions, overwrite another agent's work, or add a permanent "consistent API" wrapper.

## 11. Refactoring and migration sequence

### 11.1 Work packages and dependency gates

| Phase | Deliverables | Exit gate |
|---|---|---|
| P0 — Record actual behavior | Enumerate declaration forms, operator behavior, type identities, suffixes, real channel/TCP owners, effect inference call sites, and active parser/backend paths | Source inventory plus executed characterization tests; legacy versus production paths labeled |
| P1 — Canonical `unit` representation | Reuse type interner/layout authority; canonical declaration AST with orthogonal metadata; compatibility lowering from old forms | Both spellings yield equivalent semantic facts for migrated declarations |
| P2 — Parser and keyword migration tooling | CPU/tree-sitter/GPU grammar update; role-preserving LSP/CLI provider; formatter/docs/glossary changes | Positive/negative grammar tests and clean previewed migrations |
| P3 — Invariant/effect hardening | Unknown handling, allocation/capture effects, postconditions, summary completeness, conditional target facts | No false purity/no-allocation/state claims in the negative test suite |
| P4 — Typed standard endpoints | Payload-bound channel creation; observable send failures; local lifecycle/half-close wrappers; safe FFI imports | Wrong payload, post-close use, duplicate endpoint, and ownership error paths rejected |
| P5 — Protocol and alias safety | Optional finite session descriptors, transition validation, supported alias/capture constraints | Protocol-order and cancellation cases pass; unsupported revocation fails conservatively |
| P6 — Analysis modes and tooling | Budgeted debug/invest/CI jobs; evidence provenance; LSP state/effect views; shared CLI/MCP routes | No deep jobs on normal compiler or LSP typing path; stale edits/proofs rejected |
| P7 — Library/caller migration and retirement | Apply reviewed plans to actual source, regenerate bindings, update tests/docs; retire legacy keyword spellings in the selected language version | Declared scope clean across supported engines/backends; rollback plan retained |

P1 enables P2. P3 can proceed alongside P2 once metadata ownership is agreed. P4 depends on reliable generic/ownership rules; P5 depends on P4. Tooling query views can arrive early, but must label partial evidence. Do not gate basic safety repair on completing advanced revocable capabilities.

### 11.2 Keyword migration rules

```text
newunit Name: T as suffix     -> unit Name: T as suffix
newtype Name <existing form>  -> unit Name: T <preserved body/attributes>
existing measurement unit    -> same measurement unit form
existing alias, if migrated  -> unit Name = ExistingType
```

The `newtype` row is a semantic mapping, not a global text substitution. The migration provider first resolves the actual parser form and owner. It must preserve generics, visibility, attributes, methods, operator policy, representation, invariant attachment, and source trivia.

Recommended rollout:

1. Accept old/new spellings temporarily and lower them to one canonical representation.
2. Emit a deprecation warning with a mechanical fix only when semantic equivalence is established.
3. Update examples, generators, source templates, and formatter output to produce only `unit`.
4. Migrate packages with preview, affected-target checks, and recorded edit plans.
5. Promote the deprecation to an error in the chosen language/grammar version.
6. Keep old-cache readers only for an explicitly bounded compatibility window; invalidate or translate schemas deliberately.

Do not redefine existing symbols or silently change mangling solely because a keyword changed. Preserve canonical declaration identity under a pure syntax migration. A changed semantic rule, predicate, scale, ownership contract, or ABI commitment is an actual compatibility change and must invalidate relevant caches and callers.

### 11.3 State and endpoint migration rules

- Inventory old call shapes and distinguish real runtime wrappers, simulations, legacy bootstrap code, and user-defined methods with coincident names.
- Replace independently generic channel methods with endpoint-bound payload types; infer `T` only when all relevant uses agree.
- If one channel intentionally carries multiple message kinds, propose an existing sum type. Do not guess a common unchecked dynamic type.
- Propagate newly observable send/receive errors through real callers. Never insert silent fallback/discard handling to make the build green.
- Keep protocol sequencing opt-in for channels that actually implement a sequence-dependent protocol.
- Public API/FFI changes require an explicit compatibility decision. Temporary migration shims, if unavoidable, have a removal gate; they are not the end-state design.
- Make async/backend behavior explicit in summaries; a re-export does not automatically convert blocking calls to suspension.

### 11.4 No unsafe warning-period optimizer assumptions

The warning period permits migration work; it does not permit optimization based on predicates, effects, or states that have not been established. Keep necessary runtime behavior or diagnostics until the strict invariant is real.

Promotion to error is a policy switch after coverage is validated, not a proof by itself. Require end-to-end negative tests and evidence for each promoted rule. Never "fix" the audit by globally disabling the diagnostic or erasing an unknown summary.

### 11.5 Rollback and concurrent work

All source changes are previewable/versioned edit plans. Rebase semantic edits against changed snapshots; never overwrite another agent's collection or API work. Restore only files owned by the accepted plan if a rollback is needed.

Keep grammar, semantic schema, and library API migration versions explicit. A failed migration cannot publish a partially updated summary/cache as if it were complete.

## 12. Acceptance tests and performance gates

### 12.1 Required SSpec groups

Assign stable requirement/test IDs and connect them to the existing feature/requirement traceability system. Include compile-pass, compile-fail, runtime-result, and artifact-inspection tests; one kind does not substitute for another.

| Test ID | Required case and expected evidence |
|---|---|
| UNIT-01 | Old `newunit` and migrated `unit` preserve semantic ID, literal suffix, overload resolution, and ABI where promised |
| UNIT-02 | Old `newtype` preserves supported methods/operators and visibility; ambiguous migrations stop with a preview diagnostic |
| UNIT-03 | Alias remains the same type; nominal declaration remains distinct even with identical representation |
| UNIT-04 | Same-dimension conversions succeed under documented rules; incompatible dimensions and unrelated IDs fail |
| UNIT-05 | Inexact/narrowing/overflow conversion is diagnosed or returned as a typed error; no silent validity bypass |
| UNIT-06 | `Port.try_from(u64(65537))` does not truncate to an apparently valid `Port(1)`; representability is checked before narrowing |
| UNIT-07 | Invalid scalar constants cannot use an unchecked refined constructor; checked construction may return a valid error result |
| UNIT-08 | Predicates survive assignment, deserialization, macro expansion, FFI import, and mutation; no forged state marker casts |
| UNIT-09 | More than 16 custom types work; duplicate/collision handling uses canonical identity, not unchecked hash equality |
| UNIT-10 | Target ABI alignment comes from the layout engine; 32-/64-bit and OS/CPU variations covered |
| PARSE-01 | Unit forms, nested generics, invariant bodies, aliases, suffixes, and derived units have equivalent CPU/tree-sitter/SIMD/GPU parse results where backends exist |
| PARSE-02 | Malformed/ambiguous headers produce stable diagnostics; no symbol-table-dependent parser backtracking introduced |
| INV-01 | A debug-only assertion cannot justify a release refinement, niche, state transition, or optimizer assumption |
| INV-02 | Error return, cancellation, reentrancy, and suspension do not expose temporarily broken invariants |
| INV-03 | `old()` captures only needed values; removed checks do not leave hidden allocations/snapshots |
| EFF-01 | I/O is traced from resolved symbols, not a function called `send`; simulated buffer code is not mislabeled solely by namespace |
| EFF-02 | Direct, recursive, generic, closure, method, trait-object, and FFI calls preserve sound effect upper bounds |
| EFF-03 | Unknown HIR/callee/foreign behavior never becomes an empty or falsely complete effect row |
| EFF-04 | Closure creation and invocation have distinct effects; backend-created allocation and cleanup are included |
| EFF-05 | Different backend implementations have distinct resolved effects; shared HIR is not mutated |
| CHAN-01 | Sending `Request` and receiving `Response` on the same ordinary typed queue fails unless an explicit sum/protocol permits it |
| CHAN-02 | Closed/full/rejected send is observable and returns correct message ownership; no silent drop |
| CHAN-03 | Global concurrent closure is handled at runtime; buffered messages drain as specified |
| STATE-01 | Use after consuming close, double transition, invalid half-close operation, and illegal clone/cast fail statically |
| STATE-02 | Alias in a field or closure cannot outlive required permission; unsupported revocation is not accepted silently |
| STATE-03 | Borrow/lifetime/variance and thread-transfer facts remain correct after marker erasure |
| SESSION-01 | Wrong direction, payload, continuation, or branch fails; dual endpoints agree |
| SESSION-02 | Recursive protocols use bounded finite graph processing rather than unbounded generic instantiation |
| SESSION-03 | Cancellation before/after commit and partial I/O produce the declared owned continuation; no duplicate delivery assumed safe |
| FFI-01 | Raw handle imports cannot forge payload or lifecycle types; declared ABI and actual implementations agree per target |
| FFI-02 | Dynload/hot replacement rejects incompatible type/effect/state contracts before activation |
| MIR-01 | Mandatory structural checks remain enabled in normal/release; expensive pass-by-pass proof is mode-gated |
| MODE-01 | Normal/release compile and LSP keystrokes launch no heavyweight solver/model checker |
| MODE-02 | Analysis-mode timeout/cancel/unsupported results are unknown and do not produce success certificates |
| CACHE-01 | Body/spec/dependency/policy/compiler/target changes invalidate affected evidence; comment-only handling follows versioned canonicalization |
| CACHE-02 | A fabricated/stale `verified=true` record cannot establish an invariant; valid proof admission follows its documented trust boundary |
| LSP-01 | Hover/effect/state views agree with compiler diagnostics, target, source snapshot, and completeness |
| LSP-02 | AST find/change helpers preserve comments, bindings, evaluation order, and nominal semantics |
| LSP-03 | Code-action resolution is lazy; stale plans fail validation; multi-file partial failure does not claim success |
| LSP-04 | No unattended fix removes a restriction, adds an unproved contract, retries I/O, or invents protocol actions |
| CLI-01 | LSP/CLI/MCP produce equivalent plans and diagnostics for the same snapshot; preview is nonmutating |
| INTEGRATION-01 | Changing collection method names/parameters/extensions triggers correct caller migration without altering the owning agent's implementation |

### 12.2 Benchmark protocol

Measure before/after on the same host, target, optimization level, and changed-source set. Report cold, warm, and incremental compilation separately. Do not compare a proof-enabled CI build to a proof-disabled release build as evidence of compiler speed.

Required workloads:

- Thousands of nominal/measurement declarations and refined scalar constructions.
- Long call chains, recursion SCCs, callbacks, and a small set of unknown foreign calls.
- Payload channels and fixed-state resource wrappers.
- Deep and recursive protocol descriptors to expose generic expansion.
- Invariants over scalar fields and large collections.
- Ordinary LSP hover/action queries and migration previews while files are changing.
- A representative compiler/build-runner path and a representative SOSIX/device path.

Record wall time, peak memory, number of reanalyzed functions, summary-cache hit rate, output code size, runtime allocations, relevant instruction sequences, and LSP latency percentiles. Any numeric budget chosen later is an engineering acceptance target, not a measurement in this report.

### 12.3 Nonnegotiable performance gates

1. Ordinary builds do not start a heavy verification process.
2. Metadata queries reuse canonical summaries; LSP does not rescan the workspace for each hover.
3. Primitive-backed units do not require a new heap object or per-value nominal tag.
4. A static state marker does not add a stored field or dispatch branch solely for type checking.
5. Necessary conversions and boundary checks are measured separately, not hidden in a "zero overhead" claim.
6. No expensive full-collection invariant rescan is inserted automatically into a normal hot-path operation.
7. Deep work is bounded/cancellable and does not block typing, normal compile, or ordinary interpreter evaluation.
8. Any interpreter representation overhead is reported honestly; source type erasure alone is not proof of identical interpreter cost.

### 12.4 Formal assurance boundary

Tests support implementation quality; they do not establish all-execution properties. If a guarantee depends on a formal result, connect the proof to the real lowered program and concrete interface assumptions.

Use existing Lean/verification integration rather than creating a new proof front end. Target a small trusted admission/kernel boundary, explicit foreign assumptions, and regression tests for previously unsupported forms. Do not claim the whole language verified because a model of one rule has been proved.

## 13. Research decisions

The following are primary-source design inputs. Performance results from a research prototype are not predictions for Simple.

| Research / reference | Useful idea for Simple | Adopt now | Keep outside the normal fast path |
|---|---|---|---|
| F# units of measure [R3] | Compile-time dimensional checking with erased unit metadata | Normalized dimension metadata and type-directed diagnostics | No new solver; real scaling still costs arithmetic |
| Koka, effect types (2014) [R4] | Infer possible behavior and compose it through function calls | Conservative summaries using existing effect rows | Do not add algebraic-effect runtime handlers merely to track I/O |
| Flux, PLDI 2023 [R8] | Refinements work with ownership; inference reduces annotation burden for selected cases | Cheap local facts and optional contract suggestions | SMT/liquid inference only in the allowed analysis modes |
| Ferrite, ECOOP 2022 [R5] | Generic continuation types for protocol fidelity; linear and shared-session discipline | Optional finite protocol descriptors over typed channels | Complex shared/multiparty verification and global progress proofs |
| Typestate via Revocable Capabilities, PLDI 2026 [R6, R7] | Resource-specific permission dependencies can track state changes through aliases | Borrow-based subset and conservative invalidation | Full higher-order/shared revocation until sound support is demonstrated |
| Thrust, PLDI 2025 [R10] | Propagate refined facts back through mutable borrow release; modular invariant reasoning | Correct fact invalidation and restoration around borrows | CHC solving/prophecy-based deep verification |
| RefinedRust, PLDI 2024 [R11] | Foundational verification must cover unsafe implementations behind safe APIs | Explicit trusted boundary and typed implementation contracts | Proof-assistant verification of complex runtimes/containers |
| Rust phantom types [R2] | Zero stored size does not erase ownership/lifetime significance | Preserve semantic marker facts during lowering | No runtime marker objects solely for static identity |

### 13.1 Additional strong-type applications using the same mechanisms

No additional keywords are needed for these follow-on uses:

| Application | Expression using existing mechanisms | Main benefit / caveat |
|---|---|---|
| Bytes versus sectors | Distinct `unit ByteCount: u64` and `unit SectorCount: u64` | Explicit device-specific conversion; sector size is not universally constant |
| Device/region-specific handles | Generic brand on a nominal handle | Prevent cross-device/region mixing; reusable pool generations may still require runtime validation |
| Host versus GPU resources | Existing generic memory-space/resource type plus transfer effects | Prevent wrong-address-space use; do not assume raw integer handles carry the proof |
| Validated parsing | Ordinary input type followed by checked construction of a refined type | Separate untrusted data from established invariants |
| Invariant-preserving collections | Existing collection type/traits with verified constructors and mutators | Avoid repeating expensive checks; unrestricted mutation cannot keep the guarantee |
| Queue lifecycle | Generic state plus noncopyable ownership | Prevent local submit-after-close; not a substitute for device-completion/error checks |

These are applications of the proposed shared metadata, not a mandate to implement a general dependent-type language or to redesign the other collection workstream.

### 13.2 What to defer explicitly

- General higher-order theorem proving during everyday compilation.
- A new dependent/session/capability language surface.
- Full revocable-capability semantics copied from an incomplete prototype.
- Global deadlock or distributed-protocol correctness claims based only on local types.
- Solver-driven automatic rewrites of business/protocol behavior.
- Universal elimination of runtime checks at foreign, concurrent, or device boundaries.

The practical advantage over baseline Rust should come from coherent standard APIs, strict conservative checking, and better automatic tooling—not from adding more syntax or claiming that one paper solves every safety problem.

## 14. Glossary

Update the project glossary and LSP terminology together.

| Term | Meaning in this plan |
|---|---|
| Unit declaration | The single source declaration surface for the merged roles |
| Nominal type | A type with a distinct semantic identity even if its storage matches another |
| Alias | Another name for the same type; no new nominal identity |
| Measurement / dimension | Physical or domain quantity algebra plus conversion metadata |
| Refinement | A predicate restricting valid values of a type |
| Invariant | A property that must hold at specified observable boundaries |
| Contract | A relationship between inputs, outputs, state, and outcomes |
| May-effect | A conservative description of behavior a computation may perform |
| Unknown effect | Missing/unmodeled evidence; never synonymous with no effects |
| Latent effect | Behavior of a callable when invoked, distinct from constructing/capturing it |
| Typestate | A compile-time distinction between legal local resource states |
| Session type | An ordered communication protocol with typed continuations |
| Capability | A permission tied to a resource; not necessarily stored at runtime |
| Revocation | Removal of a previously justified permission after a transition |
| Phantom/state marker | A semantically meaningful type parameter without a stored value field |
| Invest | Investigation/inspection build mode for selected deep analysis |
| Diagnostic invariant | A check for investigation/testing that is not automatically a release type fact |
| Proof artifact | Evidence bound to a precise program/specification and checked/admitted under a defined trust model |
| Semantic autofix | A validated AST/CST edit plan based on resolved facts, not a textual guess |

`newunit` and `newtype` become legacy migration terms. Keep search redirects in documentation and migration help until the compatibility window closes.

## 15. Delivery checklist and source index

### 15.1 Implementation completion checklist

- [ ] One canonical `unit` AST/semantic description; legacy spellings lower into it during migration.
- [ ] Nominal, alias, measurement, predicate, and state facts remain distinct and composable.
- [ ] Scalable type interning and target-correct layout replace fixed helper assumptions.
- [ ] Existing invariant/effect code is integrated and hardened with explicit unknown states.
- [ ] Typed channel payloads and observable errors precede advanced session typing.
- [ ] TCP/local resource transitions, aliases, cancellation, and cleanup have defined ownership outcomes.
- [ ] High-overhead checking and tracing occur only in debug/invest/CI.
- [ ] Normal/release safety and structural checks cannot be disabled by choosing a faster mode.
- [ ] LSP/CLI/MCP expose the same type/effect/state facts and shared migration providers.
- [ ] Refactors preserve semantics or require explicit review of the behavior change.
- [ ] SSpec tests cover every requirement group, including unsupported/unknown cases.
- [ ] Benchmarks establish the actual costs before any performance claim.
- [ ] Documentation and glossary use `unit`; legacy keywords are retired by an explicit version gate.

### 15.2 Primary language and research references

**R1. Rust Reference — Behavior not considered unsafe.**  
https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html  
Use: comparison boundary for logic errors, deadlocks, and resource leaks; not an assertion that Rust lacks all higher-level verification tools.

**R2. Rust standard library — `PhantomData`.**  
https://doc.rust-lang.org/std/marker/struct.PhantomData.html  
Use: zero-size type markers still participate in safety properties.

**R3. Microsoft F# documentation — Units of Measure.**  
https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/units-of-measure  
Use: dimensional checking and erased metadata; actual conversion arithmetic is a separate issue.

**R4. Daan Leijen — Koka: Programming with Row Polymorphic Effect Types (2014).**  
https://www.microsoft.com/en-us/research/publication/koka-programming-with-row-polymorphic-effect-types-2/  
Use: inferred/compositional effect types. This plan does not adopt a handler runtime.

**R5. Ruo Fei Chen, Stephanie Balzer, and Bernardo Toninho — Ferrite: A Judgmental Embedding of Session Types in Rust (ECOOP 2022).**  
https://arxiv.org/abs/2009.13619  
Author-maintained protocol documentation: https://ferrite-rs.github.io/ferrite-book/02-main-concepts/01-protocols.html  
Use: session continuations and explicit discipline for shared protocols.

**R6. Songlin Jia and colleagues — Typestate via Revocable Capabilities (PLDI 2026).**  
https://pldi26.sigplan.org/details/pldi-2026-papers/80/Typestate-via-Revocable-Capabilities  
DOI: https://doi.org/10.1145/3808323  
Use: alias-sensitive permission/state research; not a production-readiness endorsement.

**R7. Authors' artifact for Typestate via Revocable Capabilities.**  
https://zenodo.org/records/19614655  
README: https://zenodo.org/records/19614655/preview/README.md?include_deleted=0  
Use: documented prototype limitations, examples, and compiler-benchmark method. No Simple performance result is inferred.

**R8. Nico Lehmann and colleagues — Flux: Liquid Types for Rust (PLDI 2023).**  
https://pldi23.sigplan.org/details/pldi-2023-pldi/64/Flux-Liquid-Types-for-Rust  
DOI: https://doi.org/10.1145/3591283  
Use: refinement inference combined with ownership.

**R9. Microsoft — Language Server Protocol.**  
https://microsoft.github.io/language-server-protocol/  
Specification: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.18/specification/  
Code actions: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/lsp/3.18/language/codeAction.md  
Use: standard transport/capability mechanisms; Simple semantic queries remain negotiated extensions.

**R10. Hiromi Ogawa, Taro Sekiyama, Hiroshi Unno — Thrust: A Prophecy-Based Refinement Type System for Rust (PLDI 2025).**  
https://pldi25.sigplan.org/details/pldi-2025-papers/84/Thrust-A-Prophecy-Based-Refinement-Type-System-for-Rust  
DOI: https://doi.org/10.1145/3729333  
Use: modular reasoning about mutable borrows and deep invariant inference.

**R11. Lennard Gäher and colleagues — RefinedRust: A Type System for High-Assurance Verification of Rust Programs (PLDI 2024).**  
https://plv.mpi-sws.org/refinedrust/  
Paper: https://iris-project.org/pdfs/2024-pldi-refinedrust.pdf  
Use: foundational checking of safe/unsafe implementation boundaries.

### 15.3 Repository evidence locator

Pinned tree: https://github.com/ormastes/simple/tree/97700b29e10675867891503f1e634b50a192356d

Source paths and observed behavior are listed in section 2. Reviewers can resolve each path under that immutable revision; re-resolve ownership before implementing on a later branch.

The research supports design choices. The source audit establishes selected existing code. Neither substitutes for the acceptance evidence in section 12.

---

**Final implementation direction:** Consolidate declarations into `unit`; strengthen existing type, contract, effect, and ownership machinery; migrate the actual standard-library boundaries; expose understandable, actionable facts through one LSP/CLI/MCP service; and reserve expensive verification for debug/invest/CI without weakening ordinary safe semantics.
