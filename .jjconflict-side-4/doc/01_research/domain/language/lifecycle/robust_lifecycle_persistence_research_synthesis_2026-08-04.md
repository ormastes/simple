# Simple Robust Lifecycle, Persistence, Recovery, and Power-Failure Model

**Subtitle:** Language grammar, object/entity handles, memory sections, boot and reload semantics, bare-metal runtime support, AOP hardening, and Lean 4 verification  
**Status:** Research synthesis and proposed complete design  
**Date:** 2026-08-04  
**Repository examined:** `ormastes/simple`, `main`  
**Repository snapshot observed during research:** through commit `de8330d1174925dd3a6a0a53ffd42f708c53e34e`  
**Suggested repository destination:** `doc/05_design/language/lifecycle/robust_lifecycle_persistence_design_2026-08-04.md`

---

## 1. Executive decision

Simple should add a first-class **lifecycle domain system** for software state that must remain valid across process restart, service reload, reset, suspend, hibernation, sudden power loss, firmware update, factory reset, and device replacement.

The syntax must follow Simple's existing declaration style:

- a declaration header ending in `:`;
- an indented body;
- normal Simple `struct`, `enum`, `trait`, function, contract, and attribute syntax;
- no new lifecycle block written with `{...}`;
- no separate mini-language for recovery algorithms when ordinary Simple functions and enums are sufficient.

The final design has three small new declaration forms:

```simple
life DeviceLife:
    call
    task survives call
    process survives task
    service_restart survives process
    warm_boot survives service_restart
    cold_boot survives warm_boot
    power_loss survives cold_boot
    firmware_update survives power_loss
    factory_reset survives firmware_update

virtual life HostBound:
    base: power_loss
    requires: same_host_identity
    invalidated_by: controller_replacement

recovery NamespaceRecovery for NamespaceState:
    schema: 3
    codec: NamespaceCodec
    validate: validate_namespace
    migrate: migrate_namespace
    recover: recover_namespace
    clean_start: clean_namespace
    reconcile: reconcile_namespace
```

A fourth declaration, `transition`, is recommended because a lifecycle order alone does not describe what a particular reset or power event destroys:

```simple
transition SuddenPowerLoss:
    crosses: power_loss
    kind: crash
    volatile: lose
    retained: PlatformRetention
    persistent: MetadataFlashFailure
    environment: may_change
    restart: reset_vector
```

Everything else should reuse current Simple mechanisms:

- `struct` and `enum` for state and recovery state machines;
- `@section` and the linker SDN for physical placement;
- current contracts `in:`, `out(ret):`, `out_err(err):`, `invariant:`, and `decreases:`;
- `@verify`, generated Lean, and durable handwritten Lean theorem files;
- current AOP `on pc{...} use ...`, `forbid pc{...}`, and `allow pc{...}` for cross-cutting hardening;
- current strictness tiers `moderate`, `strict`, `robust`, and `critical`;
- current runtime handle spelling `+T`, but with a strengthened pool/epoch implementation;
- new `EntityId<T>` and `EntityRef<T>` for identity that survives reload or reboot.

The central rule is:

> A long-lived object may contain a strong reference only to state whose lifecycle is equal or longer. A reference to shorter-lived state must explicitly say how it is resolved again, rebuilt, observed as environment, or treated as optional.

The proposed core field types are:

```simple
mapping_root: EntityRef<MappingRoot>
cache: Rebuild<MappingCache>
scheduler: Rebind<IoScheduler>
host: EnvRef<NvmeHost>
previous: WeakEntityRef<NamespaceState>
```

Unwrapped fields are authoritative state of the containing managed entity by default. This avoids adding field attributes before the current field parser is ready. Prefix field attributes can be added later as syntax sugar.

The design explicitly separates:

1. **execution lifetime** — stack, heap, ownership, borrowing, current `+T` handles;
2. **survival lifecycle** — which reset or power boundary logical state survives;
3. **storage domain** — RAM, retained RAM, NVM, flash, block storage, remote storage;
4. **identity domain** — address, runtime handle, boot-stable ID, persistent entity ID;
5. **validation state** — decoded, validated, reconciled, active;
6. **operational typestate** — uninitialized, ready, quiesced, recovering, degraded;
7. **boot phase** — what services and hardware capabilities are available.

These dimensions interact, but none should be collapsed into a single integer or a single `persistent` qualifier.

---

## 2. Scope

This design covers:

- ordinary application objects;
- Simple OS services and device drivers;
- bare-metal firmware;
- NVMe controller firmware and NAND metadata;
- retained-memory MCUs;
- byte-addressable persistent memory;
- block and flash storage;
- suspend, hibernate, restart, hot reload, and firmware replacement;
- typed handles and stable entity references;
- serialization, schema migration, validation, recovery, clean start, and reconciliation;
- compile-time dependency checks;
- crash-fault injection and system testing;
- generated Lean 4 models and proof obligations.

It does not claim that one persistence mechanism is optimal for every backend. Journaling, undo logging, redo logging, copy-on-write, double buffering, task atomicity, and snapshots are backend strategies beneath one language-level safety contract.

It also does not claim that current Simple verification can already prove the complete design. The current `@verify` workflow is strongest for pure functions and bounded language subsets. This document defines the additional semantic model and refinement work required for hard crash verification.

---

## 3. Current Simple audit

### 3.1 Grammar conventions

Current Simple declarations use a colon followed by indentation:

```simple
struct Point:
    x: i64
    y: i64

fn length(p: Point) -> i64:
    ...
```

The parser implements `Colon`, `Newline`, `Indent`, and `Dedent` as the ordinary block mechanism. Current domain declarations such as `handle_pool` also use indentation:

```simple
handle_pool Enemy:
    capacity: 1024
```

Braces appear in some existing specialized constructs, collection literals, enum struct variants, metadata compatibility blocks, assembly forms, embedded Lean, and AOP pointcuts. They are not the correct style for the new lifecycle declaration family.

**Decision:** lifecycle, virtual lifecycle, transition, and recovery declarations use only colon-and-indentation blocks.

### 3.2 Attributes

Simple already supports prefix attributes such as:

```simple
@section(".vector_table")
@align(512)
var vector_table: VectorTable
```

The parser has a known-attribute path and supports attribute arguments. The new feature should extend that path with:

```text
life
identity
codec
recovery
stateless
power_atomic
intermittent_task
hibernate_state
persistent_root
```

Current attributes before structs, classes, functions, and global declarations are a natural integration point.

### 3.3 Field parser limitation

The current struct/class field parser expects a field directly:

```simple
name: Type
var count: i64
```

Inside a type body, a leading `@` is currently routed primarily as a method decorator. Therefore this form is not safely compatible with the current parser without an AST and parser extension:

```simple
@rebuild(build_cache)
cache: MappingCache
```

**Decision:** the phase-1 core uses wrapper types:

```simple
cache: Rebuild<MappingCache>
scheduler: Rebind<IoScheduler>
host: EnvRef<NvmeHost>
```

Phase 2 may add field attributes as sugar, lowering them to the same lifecycle IR.

### 3.4 Existing memory and handle model

Current Simple distinguishes ordinary values and pointer/ownership forms including `&T`, `*T`, `@T`, `-T`, and `+T`. Current handle pools use an index/generation design and expose `+T`.

That is useful for stale-handle detection inside one runtime, but it is not a persistent entity identity. A raw runtime handle cannot safely be serialized and restored after:

- a pool is reconstructed;
- slots are reordered;
- generation counters reset;
- firmware changes layout;
- a process or device reboots.

**Decision:** keep `+T` as an activated runtime handle and add a separate stable-reference family.

### 3.5 Linker and memory sections

Simple already has:

- `@section("...")`;
- board-level SDN memory regions;
- SDN section mappings;
- generated linker-script plans;
- startup/data/BSS/heap/stack concepts;
- backup SRAM examples;
- module-level linker placement.

This is the correct physical-placement layer. Lifecycle support should extend the board/section schema rather than invent physical addresses in language syntax.

### 3.6 AOP

Simple already uses:

```simple
on pc{ execution(* target_func(..)) } use advice_func before priority 10
forbid pc{ import(test.internal.*) } "Production cannot import test internals"
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"
```

The AOP design already recognizes that verification must operate on the post-weaving representation.

**Decision:** lifecycle grammar does not embed a second pointcut syntax. Hardening rules are generated into or implemented through the existing AOP facility.

### 3.7 Strictness tiers

Current Simple separates runtime/memory-library selection from lint strictness. `robust` and `critical` are the correct enforcement profiles for lifecycle rules.

**Decision:**

- `moderate`: lifecycle diagnostics are mostly advisory;
- `strict`: unsafe persistent references and malformed recovery metadata are errors;
- `robust`: all lifecycle safety rules are errors; proof coverage is reported;
- `critical`: robust rules plus required discharged proofs, no unlisted trusted assumptions, and release-gate evidence.

### 3.8 Lean workflow

Current Simple has:

```simple
@verify
fn factorial(n: i64) -> i64:
    in: n >= 0
    out(ret): ret > 0
    decreases: n
    ...
```

Generated and handwritten proof layers are already separated in the repository guidance. This is important: lifecycle generation should produce stable definitions, while manually maintained theorems import them.

Current verified functions are expected to be pure and have bounded feature support. Storage I/O, MMIO, crashes, and nondeterministic environment transitions therefore require an explicit abstract transition model and a refinement layer; annotating the real recovery function with `@verify` alone is insufficient.

### 3.9 Current gap summary

| Area | Current useful foundation | Missing lifecycle capability |
|---|---|---|
| Syntax | Colon/indent declarations, attributes | Named life DAG, transition and recovery declarations |
| Runtime handles | `handle_pool`, `+T`, generation | Boot epoch, persistent IDs, resolver, generation-wrap policy |
| Memory | ownership/capability types | survival domains and cross-domain reference checks |
| Linker | `@section`, board SDN | lifecycle and startup policy on regions/sections |
| Serialization | generic serializers | versioned persistence contract and candidate validation |
| Recovery | ordinary functions | declarative registration, selection policy, clean-start contract |
| AOP | pointcuts and weaving | generated persistence hardening policy and proof certificate |
| Lean | contracts and generated proof workflow | crash semantics, recovery refinement, environment model |
| Testing | SSpec and system tests | exhaustive persist-event power cuts and reboot/recovery loops |

---

## 4. Research synthesis

No single prior system provides the complete requested model. The design should combine lessons from several research lines.

### 4.1 Typestate

Typestate refines a type according to the operations currently legal on an object. It is appropriate for:

```text
Decoded -> Validated -> Reconciled -> Active
OpenTransaction -> Committed
UninitializedDevice -> ReadyDevice -> QuiescedDevice
```

Typestate catches illegal operation sequences but does not by itself define:

- what survives power loss;
- persistent write ordering;
- torn writes;
- schema migration;
- stable identity after relocation;
- environment changes while power is absent.

**Design consequence:** use typestate for validation and operation phases, and lifecycle domains for survival.

### 4.2 Linear types, adoption/focus, ownership, and capabilities

Linear and capability systems are useful for ensuring that a resource has one controlling authority, transitions are not duplicated, and deallocation or state changes are legal. Vault's adoption/focus work is particularly relevant to protocol checking without forcing every containing object to become linear.

**Design consequence:** recovery tokens, transaction ownership, exclusive persistent writers, and resolver capabilities should be affine or isolated where possible. Persistent logical identity remains separate from ownership of the currently activated object.

### 4.3 Region-based memory management

Region systems make allocation domains and deallocation safety explicit or inferable. Simple already has runtime memory tiers and ownership forms.

**Design consequence:** a lifecycle domain resembles a region order, but it is not a deallocation region. A power-loss entity may be temporarily decoded in ordinary RAM; the logical entity survives even though that particular copy does not. The compiler must not conflate storage location with logical lifecycle.

### 4.4 Persistent object identifiers

PMDK demonstrates a critical rule: a persistent object reference must be a stable object identifier or offset-like handle, not a process virtual address. The mapping address may change when a pool is reopened.

**Design consequence:** persistent Simple state must not contain `&T`, `*T`, `@T`, or `+T` unless the referenced storage and ABI are explicitly proven stable across the same boundary. The normal portable form is `EntityRef<T>`.

### 4.5 Crash Hoare Logic and FSCQ

Crash Hoare Logic gives an operation both a normal postcondition and a crash condition. FSCQ showed that a storage system can be verified against crashes that occur at arbitrary points.

**Design consequence:** every persistence-relevant operation needs two semantic outcomes:

```text
normal completion -> normal postcondition
crash at any step -> crash condition from which recovery is valid
```

This is stronger than proving `serialize` and `deserialize` separately.

### 4.6 Perennial, GoJournal, and DaisyNFS

Perennial and GoJournal address concurrency together with crash safety. DaisyNFS shows the architectural value of isolating crash and concurrency reasoning in a verified transaction layer so higher layers can use simpler sequential reasoning.

**Design consequence:** Simple should provide a small verified persistence substrate. Most application and firmware code should reason over atomic transaction or journal specifications rather than manually reason about every cache flush and interleaving.

### 4.7 Argosy and recovery refinement

Argosy focuses on layered recovery and the fact that a crash can occur during recovery itself. Recovery refinements compose only under explicit conditions.

**Design consequence:** recovery is restartable, not a one-shot callback. Each layer needs an abstract recovery contract; recovery ordering and dependency composition are compiler-visible.

### 4.8 SquirrelFS

SquirrelFS uses typestate to enforce crash-consistent ordering of persistent-memory metadata updates at compile time.

**Design consequence:** Simple can encode common write-order protocols in types and effects, reducing proof burden. Typestate checks do not replace the general crash model, but they provide fast, local diagnostics.

### 4.9 DINO, Alpaca, Chain, and intermittent computing

Intermittent systems repeatedly lose power while progressing through computation.

- DINO uses checkpoints and consistency handling.
- Alpaca uses task boundaries and privatized updates committed at successful task completion, with an undo-log variant.
- Chain uses tasks and channels.
- formal intermittent-computing work shows that repeated or changing inputs can invalidate naive replay/checkpoint assumptions.
- IntOS combines threads, transactions, persistent objects, undo logging, and replay/bypass of completed interactions.

**Design consequence:** intermittent execution is not ordinary crash recovery. It needs task atomicity and explicit treatment of environment input. A sensor read, host command, or NAND observation must not be silently repeated as though it were deterministic.

### 4.10 Hibernation and power management

Linux distinguishes suspend variants and hibernation. Hibernation restores a memory image and generally assumes compatible hardware; drivers still need freeze, thaw, restore, and rebind behavior.

**Design consequence:** planned hibernation may preserve an execution snapshot, but environment handles and device resources still require validation/rebinding. Sudden power loss cannot depend on a hibernation preparation phase.

### 4.11 Firmware update, MCUboot, and SUIT

MCUboot persists progress information so an interrupted swap can resume. SUIT's architecture and manifest model emphasize compatibility, authenticity, sequence control, component dependencies, installation instructions, and resilience to update disruption.

**Design consequence:** firmware update is a lifecycle boundary above ordinary power loss. Persistent schema compatibility, anti-rollback state, migration code availability, and bootloader recovery must be modeled explicitly.

### 4.12 Theseus and stateless service boundaries

Theseus reduces the state one OS component holds for another and uses language-level mechanisms to improve live evolution and recovery.

**Design consequence:** very long-lived entities should hold authoritative domain state, not hidden state of services. They should depend on stateless service contracts, stable entity references, or rebindable service capabilities.

### 4.13 Main synthesis

The requested feature is best understood as:

> typestate + lifecycle partial order + stable identity + versioned persistence + crash logic + recovery refinement + environment reconciliation + linker/boot integration.

This combination is a credible research contribution. Existing work covers the pieces, but not this exact language-level integration for bare-metal firmware, OS services, persistent entities, hot reload, and Lean generation.

---

## 5. Terminology and semantic dimensions

### 5.1 Object execution lifetime

The period during which a concrete allocation and its address/handle are valid inside an execution instance.

Examples:

```text
expression
call
task
thread
process
service instance
boot epoch
```

This is where ordinary ownership, borrowing, deallocation, and current `+T` handles apply.

### 5.2 Lifecycle domain

A named set of boundaries across which a logical object's state must remain valid or recoverable.

Examples:

```text
service_restart
warm_boot
power_loss
firmware_update
factory_reset
```

### 5.3 Boundary

An event class that may invalidate state:

```text
process crash
controller reset
suspend
hibernate
sudden power loss
firmware activation
factory reset
device replacement
```

### 5.4 Storage domain

Where bits are kept:

```text
register
stack
heap
shared RAM
retained RAM
byte-addressable NVM
flash
block device
remote store
reconstructible state
MMIO
```

Storage durability is a physical property. Logical lifecycle is a software contract.

### 5.5 Identity domain

What “the same object” means:

```text
same address
same runtime handle
same boot epoch
same persistent entity ID
same external device identity
same replicated logical identity
```

### 5.6 Validation state

Whether data is trusted for use:

```text
RawBytes
Decoded<T>
Validated<T>
Reconciled<T>
Active<T>
```

### 5.7 Operational typestate

What operations are legal:

```text
Uninitialized
Ready
Quiesced
Recovering
Degraded
Failed
```

### 5.8 Boot phase

Which dependencies and capabilities are available:

```text
ResetVector
MinimalHardware
StorageDiscovery
RecoverySelection
StateRecovery
EnvironmentReconciliation
ServiceStart
Operational
Degraded
SafeMode
```

### 5.9 Environment

State outside the software object's persistence authority:

```text
NVMe host
NAND medium and analog read behavior
wall clock
network peer
sensor
power source
security element
external controller
```

Environment may be observable and durable, but it is not serialized as though the software owns it.



---

## 6. Design goals and non-goals

### 6.1 Goals

1. Make lifecycle dependencies statically visible and mechanically checked.
2. Keep ordinary Simple syntax and avoid a brace-based lifecycle DSL.
3. Preserve current memory-model syntax rather than replacing it.
4. Provide bare-metal operation without requiring a GC, filesystem, or dynamic allocator.
5. Make power failure possible between any two persistence-relevant steps.
6. Support planned reload and unplanned crash without treating them as identical.
7. Make stable entity identity independent of runtime addresses and runtime handles.
8. Require explicit versioning, validation, migration, recovery, clean start, and environment reconciliation.
9. Permit automatic recovery while proving every selectable result safe.
10. Prove that selected fields or objects do not need to survive a boundary.
11. Reuse current AOP and lint profiles for hardening rather than hiding semantics in advice.
12. Generate linker/startup metadata and Lean definitions from one normalized lifecycle IR.
13. Keep the trusted computing base and hardware assumptions explicit.
14. Make diagnostics useful to a human reviewer and an LLM coding agent.
15. Produce system-test evidence that survives compiler and runtime refactoring.

### 6.2 Non-goals

1. Automatically preserve every heap object across a crash.
2. Treat raw memory dumps as a portable persistence format.
3. Infer recovery policy from storage placement alone.
4. Guarantee the newest state when only safety can be established.
5. Hide irreversible data loss behind an unrestricted `clean_start`.
6. claim formal verification when proofs contain `sorry`, trusted assumptions, or unverified AOP transformations.
7. Make all services persistent.
8. Force one total lifecycle order on all platforms.
9. Expose NAND, NVMe, or host state as normal mutable software fields.
10. Require developers to write most ordinary application code directly in Lean.

---

## 7. Lifecycle order

### 7.1 Use a named partial order

A global integer level is too weak. Some domains are incomparable:

```text
security session
device calibration
replicated cloud state
firmware image
host association
factory identity
```

Simple should compile a finite directed acyclic graph.

```simple
life DeviceLife:
    call
    task survives call
    process survives task
    service_restart survives process
    warm_boot survives service_restart
    cold_boot survives warm_boot
    power_loss survives cold_boot
    firmware_update survives power_loss
    factory_reset survives firmware_update
    secure_identity survives factory_reset
    factory_calibration survives factory_reset
```

The meaning of:

```simple
power_loss survives cold_boot
```

is:

> State assigned to `power_loss` remains logically valid or recoverable across every boundary already covered by `cold_boot`, and also across a power-loss boundary.

The declaration is a DAG, not necessarily a tree:

```simple
life DistributedLife:
    request
    process_restart survives request
    node_restart survives process_restart
    replicated_commit survives node_restart
    region_failure survives replicated_commit
    audited_record survives replicated_commit
```

A level may name more than one immediate lower level:

```simple
legal_record survives region_failure, audited_record
```

This is useful when the validity domain is the join of two independent guarantees.

### 7.2 Formal order

Let `a <= b` mean that `b` survives at least every boundary survived by `a`.

For a declaration:

```simple
b survives a
```

the compiler adds:

```text
a <= b
```

and computes the transitive closure.

The compiler rejects:

- cycles;
- duplicate contradictory declarations;
- unknown parent levels;
- an unreachable level when the profile requires a rooted graph;
- ambiguous unqualified level names imported from multiple life declarations.

### 7.3 Qualification

The canonical fully qualified name is:

```simple
@life(DeviceLife.power_loss)
```

A short form is permitted when one imported life graph provides an unambiguous level:

```simple
@life(power_loss)
```

The normalized IR always stores the fully qualified name.

### 7.4 Default levels

No universal hardware-independent order should be built into the language. The standard library may provide reusable graphs:

```text
std.life.process
std.life.system
std.life.embedded
std.life.nvme
std.life.distributed
```

A product may extend or replace them.

### 7.5 Higher-level dependency rule

For a strong stored dependency:

```text
owner A strongly references dependency B
```

the type checker requires:

```text
life(A) <= life(B)
```

The dependency must be equal or higher/longer-lived than the owner.

Example:

```text
PowerLossEntity -> FirmwareUpdateEntity   legal
PowerLossEntity -> ProcessEntity          illegal
```

A shorter-lived dependency is legal only through an explicit reference form such as `Rebind<T>`, `Rebuild<T>`, `EnvRef<T>`, or `WeakEntityRef<T>`.

---

## 8. Virtual lifecycle domains

A virtual lifecycle domain expresses validity that is not determined only by physical power state.

Examples:

- configuration is valid until a schema or policy change;
- a session is valid until credential revocation;
- NAND metadata is valid only for the same geometry and media generation;
- controller state is valid only for the same host association;
- a cached model is valid until a source dataset changes.

Canonical syntax:

```simple
virtual life HostBound:
    base: DeviceLife.power_loss
    requires: same_host_identity
    requires: namespaces_compatible
    invalidated_by: controller_replacement
    invalidated_by: namespace_detach
    recover: reconcile_host_binding
```

Another example:

```simple
virtual life SchemaCompatible:
    base: DeviceLife.firmware_update
    requires: supported_schema
    invalidated_by: incompatible_layout
    invalidated_by: removed_migration
    recover: migrate_or_reject
```

### 8.1 Semantics

A physical life level is interpreted mainly through the graph order. A virtual life is interpreted as a predicate:

```text
valid_V(persistent_state, runtime_state, environment)
```

For a strong dependency from virtual domain `A` to domain `B`, the proof obligation is:

```text
valid_A(s, e) -> valid_B(s, e)
```

This is more general than comparing integers.

### 8.2 Runtime evidence

A virtual-life object should carry or derive evidence such as:

```text
host identity
media generation
schema ID
firmware class ID
security epoch
configuration digest
replication term
```

The evidence is validated during reconciliation. It must not be assumed from stale in-memory state.

---

## 9. Transition declarations

A life graph says which logical levels exist. A transition says what an event does to machine state.

### 9.1 Crash transition

```simple
transition SuddenPowerLoss:
    crosses: DeviceLife.power_loss
    kind: crash
    volatile: lose
    retained: PlatformRetention
    persistent: MetadataFlashFailure
    environment: may_change
    restart: ResetVector
```

### 9.2 Warm reset

```simple
transition ControllerReset:
    crosses: NvmeLife.controller_reset
    kind: reset
    volatile: lose
    retained: ControllerResetRetention
    persistent: preserve_committed
    environment: NvmeResetEnvironment
    restart: ControllerBoot
```

### 9.3 Planned hibernation

```simple
transition SystemHibernate:
    crosses: DeviceLife.cold_boot
    kind: planned
    prepare: prepare_hibernate
    snapshot: SystemSnapshot
    validate: validate_hibernate_image
    restore: restore_hibernate_image
    rebind: rebind_hardware
    fallback: cold_boot
```

### 9.4 Firmware activation

```simple
transition FirmwareActivation:
    crosses: DeviceLife.firmware_update
    kind: update
    manifest: FirmwareManifest
    validate: validate_update
    migrate: migrate_persistent_state
    rollback: rollback_firmware
    restart: BootloaderEntry
```

### 9.5 Transition semantics

A transition definition binds:

- a boundary to a life level;
- a transition class;
- a volatile-state rule;
- retained-memory rules;
- a persistent-storage failure model;
- permitted environment changes;
- the first boot/recovery phase;
- optional planned preparation and rollback functions.

The physical write model belongs primarily in board/storage SDN. A transition references that model. This avoids duplicating atomic-write and erase geometry in every source file.

### 9.6 Why planned and unplanned transitions differ

A planned transition may:

- quiesce devices;
- drain queues;
- take a snapshot;
- seal an image;
- record an environment fingerprint;
- cancel or complete work.

A sudden power loss may occur before any of those actions. Therefore no invariant required after sudden power loss may rely on `prepare` having executed.

---

## 10. Source-level object model

### 10.1 Keep `struct`; do not add an `entity` replacement

A Simple `struct` remains a data representation:

```simple
@codec(NamespaceCodec)
struct NamespaceState:
    id: NamespaceId
    capacity: LbaCount
    mapping_root: EntityRef<MappingRoot>
    cache: Rebuild<MappingCache>
    scheduler: Rebind<IoScheduler>
    host: EnvRef<NvmeHost>

    invariant:
        capacity > 0
```

A lifecycle-managed allocation or root is an entity over that representation:

```simple
@life(DeviceLife.power_loss)
@identity(stable, NamespaceId)
@recovery(NamespaceRecovery)
@section(".persist.namespace")
var namespace_root: PersistentRoot<NamespaceState>
```

This separation permits:

- transient candidate copies of `NamespaceState`;
- decoded old-schema values;
- tests using ordinary values;
- one persistent authoritative root;
- dynamic entities in an entity store.

### 10.2 Default field meaning

Inside a persistent entity representation:

- an ordinary field is authoritative state and inherits the entity's lifecycle;
- `EntityRef<T>` is a stable logical reference;
- `Rebuild<T>` is discarded and reconstructed;
- `Rebind<T>` is resolved again from a service registry or factory;
- `EnvRef<T>` names external state that must be rediscovered/reconciled;
- `WeakEntityRef<T>` does not keep the target logically alive;
- `SnapshotRef<T>` refers to a specific immutable version;
- `LatestEntityRef<T>` resolves to the latest acceptable committed version.

### 10.3 Phase-2 field attributes

After the field AST supports prefix attributes, these may become equivalent sugar:

```simple
@rebuild(build_mapping_cache)
cache: MappingCache

@rebind(bind_scheduler)
scheduler: IoScheduler

@environment
host: NvmeHost
```

The wrapper form remains the canonical normalized representation and remains available for generic code.

### 10.4 Life-polymorphic containers

Containers should not hard-code one lifecycle. They are lifecycle-polymorphic when their element and allocator contracts are safe:

```simple
@life_polymorphic
struct StableMap<K, V>:
    ...
```

The compiler instantiates a lifecycle parameter in the HIR even if source syntax omits it.

### 10.5 Static roots and dynamic entities

Static bare-metal root:

```simple
@section(".persist.ftl_root")
@life(NvmeLife.power_loss)
@recovery(FtlRootRecovery)
var ftl_root: PersistentRoot<FtlRootState>
```

Dynamic entity:

```simple
val id = entity_store.create<NamespaceState>(
    namespace_id,
    initial_state
)

val ref = EntityRef<NamespaceState>.new(id)
```

The allocator/store owns placement and recovery metadata. The returned persistent reference is not a direct pointer.

---

## 11. Proposed declaration grammar

This section uses a compact grammar notation with `+`, `*`, and `?` for repetition and optionality. It deliberately does not use brace notation for repetition.

```text
life_decl
    := "life" TypeName ":" NEWLINE INDENT life_item+ DEDENT

life_item
    := LifeName
     | LifeName "survives" life_name_list

life_name_list
    := QualifiedLifeName ("," QualifiedLifeName)*

virtual_life_decl
    := "virtual" "life" TypeName ":" NEWLINE INDENT virtual_item+ DEDENT

virtual_item
    := "base" ":" QualifiedLifeName
     | "requires" ":" Path
     | "invalidated_by" ":" Path
     | "recover" ":" Path
     | "proof" ":" Path

transition_decl
    := "transition" TypeName ":" NEWLINE INDENT transition_item+ DEDENT

transition_item
    := Key ":" transition_value
     | Key ":" NEWLINE INDENT transition_item+ DEDENT

recovery_decl
    := "recovery" TypeName "for" Type ":" NEWLINE INDENT recovery_item+ DEDENT

recovery_item
    := Key ":" recovery_value
     | "policy" ":" NEWLINE INDENT policy_item+ DEDENT
     | "clean" ":" NEWLINE INDENT clean_item+ DEDENT

policy_item
    := "choose" ":" ChoiceMode
     | "selector" ":" Path
     | "candidate" ":" Path
     | "fallback" ":" Path
     | "timeout" ":" Expression
     | "proof" ":" Path

clean_item
    := "preserve" ":" FieldPath
     | "reset" ":" FieldPath
     | "erase" ":" FieldPath
     | "forbid_loss" ":" FieldPath
     | "proof" ":" Path
     | "rebuild" ":" NEWLINE INDENT rebuild_item+ DEDENT

rebuild_item
    := FieldPath ":" Path
```

### 11.1 Contextual keywords

For the first implementation, `life`, `virtual life`, `transition`, and `recovery` should be recognized contextually at module item position.

Advantages:

- existing identifiers named `life`, `transition`, or `recovery` do not immediately become illegal;
- parser changes are localized;
- the syntax can stabilize before adding permanent token kinds.

After the feature is stable, they may become reserved declaration keywords if parser complexity warrants it.

### 11.2 Attribute grammar

Examples:

```simple
@life(DeviceLife.power_loss)
@identity(stable, NamespaceId)
@codec(NamespaceCodec)
@recovery(NamespaceRecovery)
@stateless
@power_atomic(FtlJournal)
@intermittent_task
```

The attribute parser should accept a qualified lifecycle path. The normalized attribute stores a resolved symbol ID, not source text.

### 11.3 No lifecycle custom block

The following is explicitly rejected:

```simple
life{power_loss}
```

So is:

```simple
lifecycle DeviceLife {
    ...
}
```

Diagnostics should say:

```text
LIFE0001: lifecycle declarations use Simple indentation blocks
help: write `life DeviceLife:` followed by an indented body
```

---

## 12. Recovery declaration

### 12.1 Canonical form

```simple
recovery NamespaceRecovery for NamespaceState:
    life: DeviceLife.power_loss
    schema: 3
    codec: NamespaceCodec
    decode: decode_namespace
    validate: validate_namespace
    migrate: migrate_namespace
    recover: recover_namespace
    clean_start: clean_namespace
    reconcile: reconcile_namespace
    activate: activate_namespace

    policy:
        choose: automatic
        selector: select_namespace_candidate
        candidate: latest_complete
        candidate: last_known_good
        candidate: replay_committed
        fallback: clean_start
        proof: namespace_selection_is_safe

    clean:
        preserve: id
        preserve: capacity
        rebuild:
            mapping_root: scan_nand_mapping
        reset: cache
        forbid_loss: user_data
        proof: namespace_clean_start_is_safe
```

### 12.2 Why this is metadata, not executable recovery syntax

The recovery declaration binds normal Simple implementations. The algorithms remain ordinary, testable code:

```simple
enum NamespaceRecoveryState:
    Discover
    Candidate(NamespaceRecord)
    Replaying(NamespaceState, JournalCursor)
    Reconciling(NamespaceState)
    Ready(Active<NamespaceState>)
    Degraded(DegradedNamespace)
    SafeMode(RecoveryFault)

fn recover_namespace(
    ctx: RecoveryContext
) -> RecoveryResult<Validated<NamespaceState>>:
    ...
```

This avoids inventing a second function language or a rigid state-machine DSL. It also lets current parser, MIR, debugger, profiler, and test infrastructure see the real control flow.

### 12.3 Required persistence operations

A durable entity contract contains more than serialization:

```text
encode
decode
validate
migrate
recover
clean_start
reconcile
activate
```

Their distinct roles are:

- `encode` — produce a canonical versioned record;
- `decode` — parse untrusted bytes into a non-active candidate;
- `validate` — establish internal invariants and record integrity;
- `migrate` — convert supported old schema versions;
- `recover` — reconstruct a safe candidate after interruption;
- `clean_start` — construct a valid state without relying on previous operational state;
- `reconcile` — compare persisted assumptions with current external environment;
- `activate` — bind runtime-only resources and produce an active object.

### 12.4 Validation typestate

`decode` must not return an active object:

```simple
fn decode_namespace(bytes: Bytes) -> Result<Decoded<NamespaceState>, DecodeError>
```

A normal path is:

```text
Bytes
  -> Decoded<T>
  -> Validated<T>
  -> Reconciled<T>
  -> Active<T>
```

Unsafe bypass requires an explicit trusted boundary and is forbidden in `robust` and `critical` application code.

### 12.5 Function contracts

```simple
@verify
fn validate_namespace_model(
    candidate: NamespaceState,
    env: NamespaceEnvModel
) -> bool:
    out(ret):
        ret implies namespace_invariant(candidate)
    ...
```

The executable I/O function may be separated from a pure model:

```simple
fn validate_namespace(
    candidate: Decoded<NamespaceState>,
    env: &NamespaceEnvironment
) -> Result<Validated<NamespaceState>, ValidationFault>:
    ...
```

The implementation must refine the pure model or a declared abstract specification.

---

## 13. Recovery policy

### 13.1 Candidate model

Recovery first discovers candidate records. A candidate carries evidence:

```simple
struct RecoveryCandidate<T>:
    state: Decoded<T>
    entity_id: EntityId<T>
    schema: SchemaVersion
    sequence: RecordSequence
    parent: Option<RecordSequence>
    integrity: IntegrityEvidence
    commit: CommitEvidence
    compatibility: CompatibilityEvidence
    source: CandidateSource
```

A candidate is not accepted merely because it has the largest sequence number.

### 13.2 Built-in policy components

The standard library should provide composable candidates:

```text
latest_complete
last_known_good
replay_committed
rollback_uncommitted
roll_forward
reconstruct_from_media
replicated_quorum
clean_start
operator_choice
host_choice
```

### 13.3 Automatic selection

Automatic selection must be deterministic under the declared model:

```simple
policy:
    choose: automatic
    selector: highest_valid_sequence
    candidate: latest_complete
    candidate: last_known_good
    candidate: replay_committed
    fallback: safe_mode
```

Required theorem:

```text
for every candidate selectable by the policy,
the accepted result satisfies the recovery invariant
```

A separate liveness or freshness theorem may show that the policy chooses the newest possible safe state. Safety does not imply maximal freshness.

### 13.4 User or host selection

```simple
policy:
    choose: operator
    selector: recovery_console
    candidate: latest_complete
    candidate: last_known_good
    timeout: 30_s
    fallback: last_known_good
```

NVMe example:

```simple
policy:
    choose: host
    selector: host_recovery_command
    candidate: latest_complete
    candidate: last_known_good
    timeout: 5_s
    fallback: safe_mode
```

Every selectable candidate must still pass validation. Operator authority does not bypass invariants unless a separately audited destructive operation is invoked.

### 13.5 Clean start

`clean_start` is not a generic “ignore errors” escape hatch.

```simple
clean:
    preserve: device_identity
    preserve: factory_calibration
    reset: runtime_statistics
    reset: queue_state
    rebuild: mapping_root by scan_nand_mapping
    erase: incomplete_update
    forbid_loss: user_data
    forbid_loss: anti_rollback_counter
```

The compiler checks that:

- every authoritative field is preserved, reconstructed, explicitly erased, or explicitly reset;
- no `forbid_loss` field is reachable from a path that selects clean start;
- required rebuild functions terminate or enter a declared safe mode;
- the clean result satisfies the type invariant.

### 13.6 Crash during recovery

Recovery itself may be interrupted. Therefore a recovery implementation must be:

- idempotent; or
- restartable from a persistent recovery cursor; or
- transactionally rolled back; or
- proven to refine a restartable lower layer.

A recovery declaration may state:

```simple
recovery MappingRecovery for MappingState:
    ...
    restart: idempotent
```

or:

```simple
recovery MappingRecovery for MappingState:
    ...
    restart: MappingRecoveryJournal
```

The corresponding proof obligation is mandatory in `critical`.



---

## 14. Runtime handle and persistent entity design

### 14.1 Keep three identity classes separate

#### Direct reference

```simple
&T
*T
@T
```

Valid only under the existing memory/ownership rules and the allocation's execution lifetime.

#### Runtime handle

```simple
+T
```

An index/generation handle into an activated pool. It may survive relocation within the same pool, but not an undeclared pool reconstruction or reboot.

#### Persistent entity reference

```simple
EntityRef<T>
```

A stable logical identity resolved after boot/reload into a runtime object.

### 14.2 Strengthened runtime handle

The current conceptual index/generation design should be strengthened to include pool identity and epoch.

```simple
struct RuntimeHandle<T>:
    pool: PoolId
    slot: SlotIndex
    generation: Generation
    epoch: PoolEpoch
```

The actual ABI may pack these fields differently by target. Required semantics:

1. `pool` identifies the resolver domain.
2. `slot` locates a current entry.
3. `generation` detects slot reuse.
4. `epoch` detects pool reconstruction or reset.
5. type identity is checked statically and, in robust dynamic boundaries, by a runtime type tag.

### 14.3 Generation wrap

A finite generation counter can eventually repeat. The implementation must choose one policy:

- sufficiently wide counter plus a proven allocation bound;
- retire a slot when its generation would wrap;
- change the pool epoch before reuse can alias an old handle;
- cryptographically/randomly generated incarnation IDs for hostile environments.

Recommended default:

```text
64-bit generation or 32-bit generation + 32-bit pool epoch
slot retirement or epoch change on wrap
```

`critical` requires a theorem or explicit platform bound showing stale handles cannot regain validity.

### 14.4 Persistent entity ID

```simple
struct EntityId<T>:
    store: StoreId
    type_id: StableTypeId
    key: StableEntityKey
```

Possible key encodings:

- monotonic integer;
- UUID-like value;
- protocol-defined ID such as namespace ID;
- composite device/media/object key.

The serialized form must not contain a process address.

### 14.5 Entity reference variants

```simple
EntityRef<T>
PinnedEntityRef<T>
LatestEntityRef<T>
WeakEntityRef<T>
SnapshotRef<T>
EnvRef<T>
ServiceRef<T>
```

Semantics:

- `EntityRef<T>` — resolve an acceptable committed generation according to the entity policy;
- `PinnedEntityRef<T>` — resolve exactly one entity incarnation/version or fail;
- `LatestEntityRef<T>` — select the latest acceptable committed version;
- `WeakEntityRef<T>` — does not imply target existence or retention;
- `SnapshotRef<T>` — immutable versioned record;
- `EnvRef<T>` — rediscover an external object and reconcile it;
- `ServiceRef<T>` — bind an implementation satisfying a service contract.

### 14.6 Activation

```simple
fn resolve_namespace(
    ref: EntityRef<NamespaceState>,
    store: &EntityStore
) -> Result<+Active<NamespaceState>, ResolveFault>:
    ...
```

Resolution validates:

- store identity;
- type identity;
- entity existence;
- record integrity;
- schema support;
- lifecycle compatibility;
- generation/version policy;
- current boot epoch;
- environment requirements.

### 14.7 Persisting a runtime handle

This is rejected:

```simple
struct ControllerState:
    worker: +IoWorker
```

when `ControllerState` is persistent.

Diagnostic:

```text
LIFE0021: runtime handle `+IoWorker` cannot be stored in a
power-loss entity

reason:
  `+IoWorker` is valid only in pool IoWorkerPool at the current pool epoch

replace with one of:
  Rebind<IoWorker>
  ServiceRef<IoWorker>
  EntityRef<IoWorkerState>
```

### 14.8 Retained RAM special case

A runtime handle in retained RAM may be valid after a warm transition only if:

- the pool storage itself survives;
- the generation table survives;
- the pool epoch survives unchanged;
- the code ABI is compatible;
- no startup code reinitializes the pool;
- the transition model explicitly permits it.

This is an exceptional proof-backed case, not the default.

---

## 15. Type and dependency rules

### 15.1 Semantic type vector

The compiler should reason about a value using orthogonal metadata:

```text
base type
ownership/capability
mutability
thread/concurrency domain
lifecycle domain
identity kind
validation typestate
operational typestate
```

The source syntax need not spell every component. The HIR must.

### 15.2 Strong field rule

Let entity `A` have life `LA` and a strong field referring to `B` with life `LB`.

Required:

```text
LA <= LB
```

### 15.3 Embedded-value rule

A directly embedded authoritative value inherits the containing entity's lifecycle unless its type is marked lifecycle-polymorphic or a field wrapper specifies another policy.

### 15.4 Pointer rule

The following are forbidden in a persistable representation by default:

```text
raw address
borrowed reference
arena-local pointer
runtime handle
function closure with captured runtime state
thread ID
file descriptor
interrupt registration token
DMA mapping
MMIO pointer
```

They may occur only inside `Rebuild`, `Rebind`, `EnvRef`, an opaque backend record with a proof-backed codec, or explicitly trusted platform state.

### 15.5 Rebuild rule

For:

```simple
cache: Rebuild<MappingCache>
```

the recovery declaration must bind a builder:

```simple
clean:
    rebuild:
        cache: build_mapping_cache
```

Required properties:

1. builder uses only dependencies available at its boot phase;
2. builder's result satisfies `CacheConsistent`;
3. persisted behavior does not depend on the old cache value;
4. repeated rebuilding is safe.

### 15.6 Rebind rule

For:

```simple
scheduler: Rebind<IoScheduler>
```

the recovery/activation metadata binds:

```text
scheduler -> bind_io_scheduler
```

Required properties:

- the binder returns a capability satisfying the service contract;
- binding failure has a declared degraded/safe-mode outcome;
- no persisted invariant assumes the prior service instance's hidden state.

### 15.7 Environment-reference rule

For:

```simple
host: EnvRef<NvmeHost>
```

the field stores only stable observation keys or reconciliation evidence, not ownership of the host.

On activation:

```text
rediscover
compare
reconcile
accept, degrade, or reject
```

### 15.8 Weak-reference rule

A `WeakEntityRef<T>` must be handled as optional at every dereference. It cannot be used to prove target retention.

### 15.9 Service dependency rule

A very long-lived top-level entity may depend on:

- a stateless service contract;
- a `ServiceRef<T>`;
- a `Rebind<T>`;
- a stable entity;
- immutable code/configuration whose own life is sufficient.

It may not strongly own the mutable runtime internals of a shorter-lived service.

### 15.10 Life-polymorphic function

A pure function that does not retain references can be lifecycle-polymorphic:

```simple
@stateless
fn checksum<T: BytesLike>(value: &T) -> Digest:
    ...
```

Its use does not create a stored dependency.

### 15.11 Escape and capture checks

A closure stored in a persistent entity is rejected if it captures:

- a shorter-life object;
- a runtime handle;
- an environment capability;
- mutable state without a stable codec.

The diagnostic should display the capture path.

---

## 16. Stateless and rebindable services

### 16.1 Stateless service

```simple
@stateless
trait ChecksumService:
    fn digest(data: Bytes) -> Digest
```

Formal meaning:

> For equal explicit inputs and equivalent declared environment observations, externally visible results do not depend on prior mutable service-instance history.

An implementation may use a cache internally only if the cache is observationally irrelevant.

### 16.2 Pure versus stateless

`pure` is stronger:

- no external observation;
- no mutable hidden state;
- deterministic in the language model.

`stateless` may use a declared environment or nondeterminism but must not require prior instance state.

Example:

```simple
@stateless
trait BlockAllocator:
    fn choose(req: AllocationRequest, env: AllocationEnv) -> Result<BlockId, AllocationFault>
```

Different valid blocks may be returned, but all results satisfy the allocation contract.

### 16.3 Rebindable service

```simple
@rebindable
trait JournalService:
    fn append(record: JournalRecord) -> Result<JournalSequence, JournalFault>
```

The service may have runtime state. A persistent entity stores:

```simple
journal: ServiceRef<JournalService>
```

not the service instance.

### 16.4 Architectural lint

For modules/classes marked as high-level durable roots:

```simple
@durable_root
struct ControllerDomain:
    ...
```

the linter enforces:

```text
direct stateful service field       deny
ServiceRef or Rebind                allow
stateless service dependency        allow
stable EntityRef                    allow
environment capability              only through EnvRef
```

This supports the user's requirement that top-level objects depend on stateless services.

---

## 17. Persistence record contract

### 17.1 Canonical record header

A general persistent record should include or derive:

```text
magic
stable type ID
entity ID
schema version
record sequence
parent/base sequence
payload length
flags
commit state
integrity digest
optional authentication tag
optional encryption metadata
optional environment compatibility digest
```

The exact wire format is backend-specific, but the semantic fields are standardized.

### 17.2 Commit evidence

A record is not accepted because parsing succeeded. The store produces `CommitEvidence` based on one of:

- atomic final commit marker;
- transaction commit record;
- double-buffer generation selection;
- journal commit sequence;
- copy-on-write root publication;
- replicated quorum evidence.

### 17.3 Integrity and authenticity

Integrity options:

```text
CRC
cryptographic digest
ECC-backed page plus digest
Merkle root
authenticated encryption tag
digital signature
```

`critical` update/security state must declare whether the threat model is accidental corruption or hostile tampering.

### 17.4 Versioning

Every durable type has a stable type ID and schema version. Field layout is not a schema.

```simple
recovery NamespaceRecovery for NamespaceState:
    schema: 3
    ...
```

Migration must be explicit:

```simple
fn migrate_namespace(
    old: VersionedDecoded<NamespaceState>
) -> Result<Decoded<NamespaceState>, MigrationFault>:
    match old.schema:
        case 1:
            migrate_v1_to_v3(old)
        case 2:
            migrate_v2_to_v3(old)
        case 3:
            old.current()
        else:
            Err(MigrationFault.unsupported(old.schema))
```

### 17.5 Migration availability

Firmware activation is rejected before switching images when the new firmware cannot:

- decode all supported current on-media schemas; or
- migrate them safely; or
- roll back to firmware that can.

The bootloader/update manifest should include a schema compatibility range and migration entry points.

### 17.6 Codec laws

At minimum:

```text
decode(encode(x)) = ValidCandidate(x)
```

for all valid `x`, modulo canonicalization.

Additional laws:

```text
encode is deterministic for canonical mode
decode rejects malformed/truncated records safely
migration preserves stable identity
migration establishes the new invariant
unknown fields obey the declared compatibility policy
```

### 17.7 Do not persist compiler layout

Unless an object is explicitly a fixed ABI hardware record with proof-backed representation, serialization must not depend on:

- host endianness;
- pointer width;
- padding bytes;
- vtable layout;
- compiler field reordering;
- raw enum discriminant accidents;
- current virtual address.

---

## 18. Persistence execution mechanisms

Language semantics should specify required atomicity and durability, not force one physical algorithm.

### 18.1 Explicit transaction

```simple
@power_atomic(FtlJournal)
fn update_mapping(
    mapping: &mut MappingState,
    change: MappingChange
) -> Result<Unit, MappingFault>:
    mapping.apply(change)
    FtlJournal.record(change)
```

The backend may lower this to redo logging, undo logging, copy-on-write, or hardware transactions.

### 18.2 Typed explicit transaction API

```simple
val tx: Transaction<Open> = journal.begin()
tx.record(change)
mapping.apply(change)
val committed: Transaction<Committed> = tx.commit()
```

An `Open` transaction cannot be discarded silently in robust modes. Scope exit must abort or produce a diagnostic.

### 18.3 Double buffer

Appropriate for small roots/configuration:

```simple
val root = DoubleBuffer<RootRecord>.open(region)
root.write_next(new_root)
root.commit()
```

Proof concerns:

- selection after torn write;
- sequence wrap;
- commit-marker atomicity;
- old copy preservation.

### 18.4 Append-only journal

Appropriate for replayable changes:

```text
intent -> data records -> commit
```

Recovery replays only committed entries and truncates or ignores incomplete suffixes.

### 18.5 Copy-on-write

Appropriate for trees and immutable structures. Publish the new root atomically after children are durable.

### 18.6 Snapshot

Appropriate for hibernation or coarse checkpoints. It still needs:

- image integrity;
- schema/firmware compatibility;
- environment fingerprint;
- rebind hooks;
- fallback boot.

### 18.7 Task atomicity

For intermittent computing:

```simple
@intermittent_task
@power_atomic(TaskJournal)
fn sample_and_update(
    sensor: EnvRef<Sensor>,
    stats: &mut PersistentRoot<Statistics>
) -> Result<Unit, SampleFault>:
    ...
```

Inputs that cannot be safely repeated must be recorded or classified as fresh/replayable.

### 18.8 Direct persistent-memory writes

Low-level operations should be effects:

```text
PersistRead
PersistWrite
PersistFlush
PersistFence
PersistCommit
```

Ordinary durable code should normally use higher-level stores. Direct operations require a platform capability and stricter proof obligations.

---

## 19. Memory sections and linker integration

### 19.1 Source and board responsibilities

Source declares intent:

```simple
@life(NvmeLife.power_loss)
@section(".persist.ftl_root")
@recovery(FtlRootRecovery)
var ftl_root: PersistentRoot<FtlRootState>
```

Board/storage SDN declares physical facts:

```sdn
memory:
    metadata_flash:
        origin: 0x08080000
        length: 256K
        permissions: rw
        life: power_loss
        write_atomic: 16
        erase_unit: 4096
        tear_model: prefix_or_none
        flush_model: controller_commit
        endurance_cycles: 100000

    backup_sram:
        origin: 0x40024000
        length: 4K
        permissions: rw
        life: deep_sleep
        retention: backup_power_valid

sections:
    .persist.ftl_root:
        memory: metadata_flash
        align: 16
        life: power_loss
        initialize: recover
        zero: never
        validate: validate_ftl_root_region
```

These fields extend the current linker SDN schema.

### 19.2 Cross-checks

The compiler/linker rejects:

- source life longer than the physical region can support;
- a persistent root in `.bss`;
- startup zeroing of a retained section;
- alignment smaller than atomic-record requirements;
- a record crossing an atomic or erase boundary contrary to its codec;
- unresolved direct relocation from a longer-life section to shorter-life mutable state;
- recovery code placed in storage unavailable during recovery;
- firmware update replacing a required migration function too early.

### 19.3 Generated startup tables

Generate:

```text
copy table
zero table
retain table
validate table
recovery table
migration table
rebind table
section lifecycle manifest
schema/type manifest
```

The reset path interprets these tables in a fixed order.

### 19.4 Section dependency rule

For mutable stored state:

```text
section A directly references section B
```

require:

```text
life(A) <= life(B)
```

Immutable code/data is checked separately for availability and update compatibility.

### 19.5 Startup initialization policy

Every nonordinary section declares one:

```text
zero
copy
retain
retain_and_validate
recover
discover
external
```

The default for unknown custom RAM sections in `robust` should be `error`, not silent zeroing.

### 19.6 Linker assertions

Generated assertions include:

- capacity;
- alignment;
- non-overlap;
- commit marker not straddling atomic unit;
- persistent record not straddling forbidden erase boundary;
- boot recovery code reachable in the boot image;
- recovery metadata retained across the declared boundary.

---

## 20. Boot and activation architecture

### 20.1 Boot state machine uses ordinary Simple

```simple
enum BootPhase:
    ResetVector
    MinimalHardware
    StorageDiscovery
    RecoverySelection
    StateRecovery
    EnvironmentReconciliation
    ServiceStart
    Operational
    Degraded
    SafeMode
```

Typed transitions:

```simple
fn init_minimal_hardware(
    boot: Boot<ResetVector>
) -> Result<Boot<MinimalHardware>, BootFault>:
    ...

fn discover_storage(
    boot: Boot<MinimalHardware>
) -> Result<Boot<StorageDiscovery>, BootFault>:
    ...
```

### 20.2 Phase capabilities

A phase grants capabilities:

```text
ResetVector
  boot ROM read
  stack setup
  minimal register access

MinimalHardware
  clock
  basic memory controller
  watchdog
  console-safe output

StorageDiscovery
  raw media reads
  metadata scan
  integrity engine

StateRecovery
  recovery journal
  migration functions

EnvironmentReconciliation
  device enumeration
  host/controller handshake

ServiceStart
  scheduler
  interrupts
  DMA
  normal allocators
```

Calling an unavailable service is a compile-time error when phase is statically known and a runtime guarded error otherwise.

### 20.3 Recovery dependency layering

Recovery layer `R_high` may call lower-level recovery `R_low` only when:

- `R_low` is available earlier;
- `R_low`'s recovery contract is established;
- crashes during `R_high` restart through the declared lower path;
- no circular recovery dependency exists.

### 20.4 Boot outcome

Boot does not need to reach full operation in every permitted failure case. The total outcome is:

```simple
enum BootOutcome:
    Operational(System)
    Degraded(DegradedSystem)
    SafeMode(SafeSystem)
    Fatal(FatalReason)
```

A formal liveness claim must explicitly state when `Operational` is guaranteed.

### 20.5 Watchdog interaction

Recovery steps must declare:

- maximum bounded work; or
- watchdog servicing; or
- persistent progress/checkpoint.

A recovery loop that can indefinitely restart without monotonic progress is rejected in `critical` unless safe-mode fallback is proven.

---

## 21. Power-management modes

### 21.1 Runtime restart

Process/service reload loses runtime allocation identity. Persisted logical state may remain. All runtime resources are rebound.

### 21.2 Warm boot/reset

Some RAM may survive, but registers, interrupt routing, DMA state, and devices may not. Retained bytes are candidates, not automatically valid active objects.

### 21.3 Suspend-to-RAM

Memory is powered, but devices are quiesced and may need resume callbacks. Runtime references may remain only under the platform transition contract.

### 21.4 Hibernation

A planned memory image is saved. On resume:

1. validate image signature/integrity;
2. validate firmware and schema compatibility;
3. validate required hardware identity;
4. restore memory;
5. invalidate or rebind external resources;
6. resume devices/services;
7. discard image or mark it consumed according to replay policy.

A hibernation image must not be treated as a sudden-power-loss recovery record.

### 21.5 Sudden power loss

No preparation is assumed. Only state covered by completed persistence events and the storage failure model is trustworthy.

### 21.6 Intermittent execution

Power loss may happen repeatedly at high frequency. Use task-atomic or transaction-based progress. Record non-repeatable input results when replay would change semantics.

### 21.7 Firmware update

Code, schemas, recovery logic, and physical layout may change. Require compatibility manifests, migration, rollback, and anti-rollback policy.

### 21.8 Factory reset

Factory reset is a policy boundary, not necessarily “erase every bit.”

Common branches:

```text
preserve device identity
preserve calibration
erase user data
reset operational statistics
preserve anti-rollback/security counters
```

The lifecycle DAG can place identity/calibration above factory reset.

### 21.9 Device replacement

Local persistent IDs may become invalid; replicated or remote identities may survive. This boundary is often incomparable with local factory reset and should not be forced into a single line.

---

## 22. Environment model

### 22.1 Environment declaration using existing traits

No new `environment` block is required in v1.

```simple
@environment
trait NandEnvironment:
    fn geometry() -> NandGeometry
    fn media_generation() -> MediaGeneration
    fn read_page(page: PageId) -> Result<PageData, NandFault>
    fn bad_block_state(block: BlockId) -> BadBlockState

@environment
trait NvmeHostEnvironment:
    fn host_identity() -> HostIdentity
    fn reset_kind() -> ResetKind
    fn attached_namespaces() -> NamespaceSet
```

### 22.2 Formal environment state

The Lean model contains:

```text
environment state
environment observations
allowed nondeterministic transition relation
```

The environment may change while the software is powered off according to the transition declaration.

### 22.3 Nondeterminism

Examples:

```text
NAND read threshold variation
newly detected bad block
torn program within declared failure model
host detach/reattach
clock advance
sensor change
network peer retry
```

The model must not replace nondeterminism with one friendly default.

### 22.4 Repeated input

An operation is classified:

```text
repeatable
record_and_replay
fresh_on_retry
idempotent_external
at_most_once_external
compensatable
forbidden_during_recovery
```

Examples:

- reading immutable geometry: repeatable after identity validation;
- reading a sensor: usually fresh or record-and-replay;
- sending a host completion: at-most-once or sequence/idempotency protected;
- programming NAND: requires media-state reconciliation, not blind replay.

### 22.5 Environment reconciliation result

```simple
enum ReconcileResult<T>:
    Compatible(Reconciled<T>)
    Migrated(Reconciled<T>)
    Degraded(DegradedState)
    CleanRequired(CleanReason)
    SafeMode(RecoveryFault)
```

---

## 23. AOP hardening

### 23.1 AOP role

AOP may enforce and instrument lifecycle rules, but it is not the semantic foundation.

The source of truth is:

```text
life graph
normalized lifecycle IR
type/effect checks
recovery contract
persistence backend specification
```

AOP adds cross-cutting guards and test instrumentation.

### 23.2 Generated policies

Examples of policy intent:

```text
forbid direct persistent writes outside approved store modules
require @power_atomic around persistent mutation entry points
forbid runtime handles in codec output
forbid external I/O in replay unless classified
inject crash probes after persistence events in test builds
require audit events for destructive clean start
```

These lower to current Simple AOP `forbid`, `allow`, and advice rules.

### 23.3 Existing pointcut syntax remains isolated

Lifecycle declarations themselves never use `{...}`. Existing AOP retains its established `pc{...}` pointcut form. This is preferable to creating a second pointcut notation inside lifecycle grammar.

### 23.4 Verify post-weaving IR

Required pipeline:

```text
parse
  -> macro expansion
  -> lifecycle normalization
  -> AOP weaving
  -> effect and dependency checks
  -> proof-model emission
  -> code generation
```

The Lean model and verification fingerprint must correspond to the post-weaving normalized IR.

### 23.5 Weave certificate

Generate:

```text
pointcut source hash
resolved join-point list
advice order
transformed function hashes
forbid/allow decisions
lifecycle policy version
compiler version
```

`critical` verification rejects a stale or missing certificate.

### 23.6 Closed proof-critical pointcuts

A proof-critical pointcut must resolve deterministically in the closed build. Dynamic future join points cannot silently alter a previously discharged proof.

### 23.7 Test-only crash advice

Power-cut injection is an excellent AOP use:

```text
after PersistWrite
after PersistFlush
after PersistFence
before/after Commit
during recovery state transitions
```

The injected test build is not the production proof artifact; the production and test weave manifests must both be recorded.



---

## 24. Lean 4 formal model

### 24.1 Verification architecture

The recommended verification chain is:

```text
Simple source
  -> normalized lifecycle HIR
  -> post-AOP MIR event model
  -> generated finite-state exploration model
  -> generated Lean definitions
  -> handwritten Lean constraints/theorems
  -> Lake verification
  -> manifest binding proofs to source, linker map, and backend assumptions
```

A bounded state explorer catches mistakes quickly. Lean provides unbounded mathematical proofs under explicit assumptions. Neither replaces the other.

### 24.2 Generated life graph

Illustrative Lean:

```lean
inductive DeviceLife
  | call
  | task
  | process
  | serviceRestart
  | warmBoot
  | coldBoot
  | powerLoss
  | firmwareUpdate
  | factoryReset
  | secureIdentity
  | factoryCalibration
  deriving DecidableEq, Repr

inductive LifeEdge : DeviceLife → DeviceLife → Prop
  | taskCall :
      LifeEdge .call .task
  | processTask :
      LifeEdge .task .process
  | serviceProcess :
      LifeEdge .process .serviceRestart
  | warmService :
      LifeEdge .serviceRestart .warmBoot
  | coldWarm :
      LifeEdge .warmBoot .coldBoot
  | powerCold :
      LifeEdge .coldBoot .powerLoss
  | updatePower :
      LifeEdge .powerLoss .firmwareUpdate
  | resetUpdate :
      LifeEdge .firmwareUpdate .factoryReset
  | identityReset :
      LifeEdge .factoryReset .secureIdentity
  | calibrationReset :
      LifeEdge .factoryReset .factoryCalibration
```

`SurvivesAtLeast` is the reflexive transitive closure of `LifeEdge`.

### 24.3 Machine state

```lean
structure MachineState where
  volatile : VolatileState
  retained : RetainedState
  persistent : PersistentState
  environment : EnvironmentState
  phase : BootPhase
  bootEpoch : BootEpoch
  poolEpochs : PoolId → PoolEpoch
```

### 24.4 Persistent events

```lean
inductive PersistEvent
  | issueWrite
  | completeWrite
  | flush
  | fence
  | publishRoot
  | commitRecord
  | erase
  | environmentRead
  | externalEffect
```

### 24.5 Step relation

Use a relation rather than one deterministic function:

```lean
inductive Step : MachineState → MachineState → Prop
  | normal :
      NormalStep s s' →
      Step s s'
  | crash :
      CrashOutcome s outcome s' →
      Step s s'
  | environment :
      EnvironmentStep s s' →
      Step s s'
```

This represents all allowed torn-write, completion, and environment outcomes.

### 24.6 Transition crash model

```lean
def CrashInvariant (s : MachineState) : Prop :=
  PersistentWellFormed s.persistent ∧
  RecoveryMetadataWellFormed s.persistent ∧
  NoActiveRuntimeHandlePersisted s.persistent
```

A sudden power-loss transition:

```lean
inductive SuddenPowerLoss :
    MachineState → StorageOutcome → MachineState → Prop
  | apply :
      LoseVolatile s.volatile volatile' →
      RetainByPlatform s.retained outcome retained' →
      ApplyStorageOutcome s.persistent outcome persistent' →
      EnvironmentMayChange s.environment environment' →
      SuddenPowerLoss s outcome
        (MachineState.mk
          volatile'
          retained'
          persistent'
          environment'
          .resetVector
          s.bootEpoch.next
          nextPoolEpochs)
```

The generated code may differ, but the model must preserve nondeterminism.

### 24.7 Recovery relation

```lean
inductive RecoveryOutcome
  | operational
  | degraded
  | safeMode
  | fatal

inductive Recovers :
    MachineState → RecoveryOutcome → MachineState → Prop
  | ...
```

Recovery may have multiple internal steps and may crash again.

### 24.8 Core theorems

#### Lifecycle graph soundness

```lean
theorem life_graph_acyclic :
  Acyclic LifeEdge
```

#### Strong reference safety

```lean
theorem strong_reference_life_safe :
  ∀ owner dependency,
    StrongReference owner dependency →
    SurvivesAtLeast (lifeOf owner) (lifeOf dependency)
```

#### Persistent pointer safety

```lean
theorem no_runtime_address_in_persistent_encoding :
  ∀ e bytes,
    Encodes e bytes →
    ContainsRuntimeAddress bytes = false
```

#### Handle epoch safety

```lean
theorem stale_handle_rejected_after_epoch_change :
  ∀ h pool oldEpoch newEpoch,
    oldEpoch ≠ newEpoch →
    h.epoch = oldEpoch →
    ResolveAtEpoch pool newEpoch h = .stale
```

#### Codec round trip

```lean
theorem codec_round_trip :
  ∀ x,
    EntityInvariant x →
    decodeCurrent (encodeCurrent x) = .ok x
```

#### Migration preservation

```lean
theorem migration_preserves_identity_and_invariant :
  ∀ old,
    OldInvariant old →
    match migrate old with
    | .ok current =>
        current.entityId = old.entityId ∧
        CurrentInvariant current
    | .error _ =>
        MigrationFailureAllowed old
```

#### Selection safety

```lean
theorem selected_candidate_is_safe :
  ∀ candidates candidate,
    select candidates = .selected candidate →
    CandidateSafe candidate
```

#### Recovery establishes an outcome invariant

```lean
theorem recovery_sound :
  ∀ s outcome s',
    Reachable s →
    CrashInvariant s →
    Recovers s outcome s' →
    OutcomeInvariant outcome s'
```

#### Recovery restart safety

```lean
theorem recovery_restart_safe :
  ∀ s r sCrash,
    RecoveryReachable s r →
    CrashDuringRecovery r sCrash →
    ∃ outcome s',
      Recovers sCrash outcome s' ∧
      OutcomeInvariant outcome s'
```

#### Clean-start loss policy

```lean
theorem clean_start_preserves_required_state :
  ∀ old clean,
    CleanStart old clean →
    RequiredIdentityPreserved old clean ∧
    ForbiddenLossPreserved old clean
```

#### Environment reconciliation

```lean
theorem reconcile_sound :
  ∀ persistent environment result,
    PersistentInvariant persistent →
    EnvironmentAssumptions environment →
    Reconcile persistent environment result →
    ReconcileOutcomeInvariant result
```

#### Boot result

```lean
theorem boot_terminates_or_enters_declared_safe_outcome :
  ∀ initial,
    BootAssumptions initial →
    ∃ outcome final,
      BootExecution initial outcome final ∧
      BootOutcomeInvariant outcome final
```

Termination may require bounded-media and watchdog assumptions, which must be named.

### 24.9 Proving a field need not survive

For a derived cache:

```lean
def ResumeWithSavedCache
    (p : PersistentState)
    (c : MappingCache) :
    ObservableBehavior :=
  ...

def ResumeWithRebuiltCache
    (p : PersistentState) :
    ObservableBehavior :=
  ...

theorem cache_not_required_across_power_loss :
  ∀ p c,
    PersistentInvariant p →
    CacheConsistent p c →
    ObservationallyEquivalent
      (ResumeWithSavedCache p c)
      (ResumeWithRebuiltCache p)
```

A stronger derived-value proof:

```lean
theorem rebuild_cache_sound :
  ∀ p,
    PersistentInvariant p →
    CacheConsistent p (buildCache p)
```

The first theorem proves non-necessity. The second proves reconstruction correctness. Both may be required for a `Rebuild<T>` field.

### 24.10 Proving a service need not survive

For a stateless service:

```lean
theorem checksum_history_independent :
  ∀ historyA historyB input,
    EquivalentDeclaredEnvironment historyA historyB →
    checksumAfter historyA input =
    checksumAfter historyB input
```

For a rebindable service:

```lean
theorem rebound_scheduler_satisfies_contract :
  ∀ environment scheduler,
    bindScheduler environment = .ok scheduler →
    SchedulerContract scheduler
```

The durable entity proves only the service contract, not service-instance identity.

### 24.11 Crash conditions on operations

A function model may expose:

```text
precondition
normal postcondition
crash condition
recovery condition
```

Conceptually:

```lean
structure CrashSpec
    (State Result : Type) where
  pre : State → Prop
  step : State → Result → State → Prop
  crash : State → State → Prop
  recover : State → RecoveryOutcome → State → Prop
```

This is the Lean analogue of Crash Hoare Logic. It should be a small Simple-specific framework, not an attempt to reproduce all of Iris/Perennial immediately.

### 24.12 Concurrency strategy

For concurrent durable code, choose one:

1. verify the transaction/journal layer concurrently and expose an atomic specification;
2. use locks/ownership to reduce higher-layer proof to sequential reasoning;
3. model full concurrent crash interleavings for selected critical components.

The default architecture should follow option 1 or 2. Full Perennial-like reasoning for every application object would be too expensive.

### 24.13 Trusted assumptions

Examples:

```text
atomic write size reported by board SDN is correct
flush/fence backend obeys its contract
boot ROM enters the documented reset phase
cryptographic primitive satisfies its declared specification
compiler lowering preserves lifecycle events
linker places sections according to the checked map
NAND model bounds match the selected device
```

Every assumption gets:

```text
stable assumption ID
owner
source/evidence
scope
affected theorems
verification status
```

`critical` release reports must list them prominently.

---

## 25. Verification assurance ladder

### Level 0 — syntax and metadata

Checks:

- life/recovery declarations parse;
- all names resolve;
- graph is acyclic;
- required recovery entries exist;
- section and schema metadata are complete.

### Level 1 — type, life, and effect checking

Checks:

- reference direction;
- no raw persistent pointer or runtime handle;
- environment and rebind wrappers;
- transaction effects;
- boot-phase capability availability;
- schema compatibility surface.

### Level 2 — bounded exhaustive exploration

Explore:

- power cut after every persistence event;
- legal torn-write outcomes;
- recovery interruption;
- bounded concurrency interleavings;
- migration paths;
- candidate-selection branches;
- environment changes.

This is a bug finder, not a proof of unbounded behavior.

### Level 3 — Lean contract proofs

Prove:

- graph/ref safety;
- codec/migration laws;
- selector soundness;
- recovery invariants;
- transient-state non-necessity;
- clean-start policy;
- environment reconciliation;
- resource bounds.

### Level 4 — MIR refinement

Show that post-weaving Simple MIR traces refine the generated abstract event model.

This is the major hard-verification milestone.

### Level 5 — backend/linker/startup refinement

Verify or tightly audit:

- persistence-instruction lowering;
- MMIO ordering;
- cache maintenance;
- linker layout;
- startup tables;
- reset assembly;
- bootloader handoff.

### Level 6 — hardware and environment validation

Validate assumptions using:

- device documentation;
- controller/NAND characterization;
- hardware fault injection;
- power-cut tests;
- protocol conformance;
- cryptographic validation.

A product may truthfully say “formally verified under assumptions A–N” only when the claimed level and proof debt are reported.

---

## 26. Compiler and toolchain design

### 26.1 Parser

Add contextual top-level recognition:

```text
life TypeName:
virtual life TypeName:
transition TypeName:
recovery TypeName for Type:
```

Do not route them through the existing generic `kind{payload}` custom-block path.

### 26.2 AST

```text
LifeDecl
  name
  levels
  direct edges
  source spans

VirtualLifeDecl
  name
  base
  required predicates
  invalidation events
  recovery path
  proof path

TransitionDecl
  name
  crossed life
  kind
  state rules
  environment rule
  restart phase

RecoveryDecl
  name
  target type
  schema
  function bindings
  policy
  clean policy
  proofs
```

### 26.3 Attribute extensions

Add normalized attributes:

```text
Life
Identity
Codec
Recovery
Stateless
Rebindable
DurableRoot
PowerAtomic
IntermittentTask
HibernateState
PersistentRoot
Environment
```

### 26.4 HIR lifecycle normalization

Produce one lifecycle IR:

```text
resolved life graph
resolved virtual predicates
entity schemas
field policies
reference edges
section assignments
transition models
recovery registrations
boot phases
effect summaries
AOP hardening requirements
proof obligations
```

All source sugar lowers here.

### 26.5 Whole-program life checker

The checker needs a graph of:

```text
types
fields
globals
allocations
sections
services
recovery functions
boot phases
module imports
AOP-transformed calls
```

It computes strong/weak/rebind/environment edges and reports the shortest violating path.

### 26.6 MIR persistence effects

Add or normalize effects:

```text
persist_read
persist_write
persist_flush
persist_fence
persist_commit
persistent_allocate
persistent_free
environment_read
external_effect
recovery_step
rebind
migration
```

Effects appear in diagnostics, AOP join-point metadata, test injection, and Lean generation.

### 26.7 Proof fingerprint

Verification-cache keys must include:

```text
source content
resolved life graph
virtual-life predicates
recovery policy
schema/codec version
section/storage model
post-weave MIR
AOP weave certificate
Lean toolchain version
backend assumption set
```

A changed board atomic-write size must invalidate relevant proofs.

### 26.8 Generated artifacts

Recommended layout:

```text
build/lifecycle/
    lifecycle_graph.sdn
    entity_manifest.sdn
    recovery_manifest.sdn
    section_lifecycle_map.sdn
    transition_models.sdn
    aop_weave_certificate.sdn
    proof_assumptions.sdn
    crash_points.sdn

src/verification/lifecycle/
    Generated.lean
    RecoveryGenerated.lean
    StorageGenerated.lean
    Constraints.lean
    Assumptions.lean
    GENERATED_CONTRACT.md
```

### 26.9 Diagnostics

Suggested stable codes:

| Code | Meaning |
|---|---|
| LIFE0001 | brace/custom-block lifecycle syntax used |
| LIFE0101 | cycle in life graph |
| LIFE0102 | ambiguous lifecycle name |
| LIFE0201 | strong dependency points to shorter life |
| LIFE0202 | raw pointer/reference in persistent representation |
| LIFE0203 | runtime `+T` handle persisted |
| LIFE0204 | generation/epoch wrap policy incomplete |
| LIFE0301 | persistent entity lacks recovery declaration |
| LIFE0302 | schema migration gap |
| LIFE0303 | decoded value activated before validation |
| LIFE0304 | clean start may lose `forbid_loss` state |
| LIFE0305 | recovery is not restart-safe |
| LIFE0401 | source life exceeds section/region durability |
| LIFE0402 | startup zeroes retained state |
| LIFE0403 | atomic record crosses unsupported boundary |
| LIFE0501 | environment object stored as owned state |
| LIFE0502 | repeated external input lacks replay classification |
| LIFE0601 | persistent write outside approved atomic/store API |
| LIFE0602 | proof-critical AOP weave certificate missing/stale |
| LIFE0701 | required lifecycle proof absent or admitted |
| LIFE0702 | backend assumption not approved for critical build |

Example diagnostic:

```text
LIFE0201: `ControllerState.worker` has a shorter lifecycle than its owner

owner:
  ControllerState at NvmeLife.power_loss

dependency:
  IoWorker at NvmeLife.service_restart

strong path:
  ControllerRoot.state -> ControllerState.worker

fix:
  use `Rebind<IoWorker>` or `ServiceRef<IoWorker>`
  or raise the dependency lifecycle when its state is truly durable
```

### 26.10 IDE and documentation support

Provide:

- hover showing resolved lifecycle;
- graph view of strong and rebinding dependencies;
- boot-phase availability view;
- persistent-record schema diff;
- migration-gap warning;
- recovery-policy visualization;
- proof-status badge;
- section/linker-map navigation;
- “why must this field survive?” and “why may this field be discarded?” trace.

---

## 27. Bare-metal runtime and library architecture

### 27.1 Modules

```text
std.lifecycle
std.persistence
std.recovery
std.entity
std.environment
std.boot
std.power
std.update
```

Bare-metal variants:

```text
nogc_sync_mut
nogc_async_mut
nogc_async_mut_noalloc
```

must provide APIs without requiring heap allocation.

### 27.2 Core types

```text
PersistentRoot<T>
EntityId<T>
EntityRef<T>
RuntimeHandle<T>
Decoded<T>
Validated<T>
Reconciled<T>
Active<T>
Rebuild<T>
Rebind<T>
EnvRef<T>
RecoveryCandidate<T>
RecoveryResult<T>
Transaction<State>
Journal<T>
DoubleBuffer<T>
Snapshot<T>
```

### 27.3 Storage traits

```simple
trait PersistentStore:
    fn read(offset: StoreOffset, out: &mut Bytes) -> Result<Unit, StoreFault>
    fn write(offset: StoreOffset, data: Bytes) -> Result<Unit, StoreFault>
    fn flush(range: StoreRange) -> Result<Unit, StoreFault>
    fn fence() -> Result<Unit, StoreFault>
    fn atomic_write_size() -> ByteCount
    fn erase_unit() -> ByteCount
```

Backend implementations:

```text
retained RAM
FRAM
NOR flash
NAND metadata log
NVMe namespace/block store
DAX persistent memory
host file/device for testing
replicated store
```

### 27.4 No-allocation recovery

Recovery APIs take caller-provided buffers and pools:

```simple
fn recover_ftl(
    ctx: &mut RecoveryContext<NoAlloc>,
    scratch: &mut RecoveryScratch
) -> RecoveryResult<Active<FtlState>>:
    ...
```

The compiler checks declared maximum scratch use in `critical`.

### 27.5 Recovery catalog

The boot image contains a static table:

```text
type ID
schema range
region/section
discover function
decode function
migration function
recovery function
reconcile function
activation function
dependency order
```

No dynamic reflection is required on bare metal.

### 27.6 Entity store

The store maps stable IDs to committed records and activated runtime handles.

```text
EntityRef<T>
  -> record discovery
  -> decode/validate/migrate
  -> active pool allocation
  -> +Active<T>
```

The activated pool is an optimization. The persistent record remains authoritative according to the store policy.

### 27.7 Bootloader subset

The earliest boot/recovery subset should support:

```text
fixed-size values
slices over preallocated buffers
checksums/digests
record scan
double-buffer/journal selection
minimal storage driver
manifest verification
rollback
safe console/error code
watchdog service
```

It should not depend on:

```text
full scheduler
normal filesystem
dynamic plugin loader
network stack
large GC runtime
ordinary service registry
```

### 27.8 Runtime observability

Each recovery emits structured evidence:

```text
transition ID
boot epoch
entity ID/type/schema
candidate list and rejection reasons
selected policy path
migration path
replayed range
clean-start actions
environment mismatches
outcome
proof/manifest hash
```

On constrained devices, this may be a compact binary ring buffer decoded by host tools.

---

## 28. Testing, fault injection, and system evidence

### 28.1 Crash-point generation

The compiler emits an ID after each relevant event:

```text
write issued
write completed
flush
fence
commit marker
root publication
erase
migration step
recovery progress step
external effect
```

A host simulator can stop at any ID.

### 28.2 Required test matrix

For each persistent operation:

1. run normally;
2. cut power before the first event;
3. cut after each event;
4. apply every bounded torn-write outcome;
5. reboot;
6. recover;
7. cut power during recovery;
8. repeat recovery;
9. compare outcome to the abstract model.

### 28.3 Storage models

Use progressively stronger evidence:

- deterministic in-memory failure model;
- file-backed real implementation with fault injection;
- QEMU/emulated controller;
- real device with debug/fault hooks;
- physical power-cut hardware-in-the-loop.

### 28.4 System tests should not mock persistence semantics

A system test may emulate a physical medium, but it should execute the real:

```text
codec
journal
commit logic
recovery selector
migration
activation path
```

Do not replace those layers with a mock that merely returns “latest record.”

When a mock is necessary, move the test down to an integration/unit boundary and do not use it as system-level crash evidence.

### 28.5 Malformed and adversarial records

Fuzz:

```text
truncation
bit flips
bad length
unknown schema
duplicate sequence
sequence wrap
invalid parent
forged commit marker
checksum collision model
wrong entity/type ID
oversized allocation request
cyclic entity references
migration bomb
recovery loop
```

### 28.6 Environment-change tests

Examples:

```text
NVMe host identity changed
namespace removed
NAND geometry changed
new bad block found
RTC moved backward
security epoch advanced
firmware rollback attempted
device resumed on incompatible hardware
```

### 28.7 Concurrency tests

Explore:

```text
writer vs checkpoint
writer vs recovery preparation
two entity transactions
GC/compaction vs reference resolution
interrupt vs commit
DMA completion vs power cut
host command completion vs reset
```

### 28.8 Wear and endurance

Test/verify:

- bounded metadata amplification;
- journal compaction;
- sequence/counter update frequency;
- double-buffer alternation;
- erase-unit balance;
- recovery scanning bounds;
- anti-rollback counter endurance.

### 28.9 Evidence artifacts

Each system run emits:

```text
build fingerprint
board/storage model
transition model
crash-point ID
write outcome
boot/recovery trace
selected candidate
final invariant check
expected model outcome
actual outcome
pass/fail
```

This evidence should be machine-readable SDN/JSON and summarized in generated Markdown.

---

## 29. Security model

### 29.1 Accidental corruption versus hostile modification

Every durable domain declares its integrity threat model:

```text
accidental
malicious_local
malicious_remote
rollback_attacker
physical_attacker
```

CRC is not authenticity.

### 29.2 Firmware and schema rollback

Use:

- signed/authenticated manifest;
- compatible device/class ID;
- monotonically controlled sequence;
- image digest;
- schema compatibility range;
- rollback image and policy;
- protected anti-rollback state.

### 29.3 Persistent reference forgery

A serialized `EntityRef<T>` includes or is validated against:

- store ID;
- type ID;
- entity ID;
- optional authority/capability;
- version policy.

Untrusted input cannot manufacture authority by constructing bytes.

### 29.4 Secrets

Declare:

```text
persist encrypted
persist sealed to device
rebuild from secure element
erase on factory reset
preserve across update
never hibernate
```

A hibernation snapshot containing secrets requires a separate encryption/replay policy.

### 29.5 Recovery downgrade

An attacker must not force “clean start” to bypass protected state. Destructive recovery requires authenticated authority or a physically defined reset policy.

### 29.6 Audit

Critical destructive actions record:

```text
reason
authority
old sequence
new sequence
fields erased
firmware/schema version
boot epoch
```

The audit itself may have a higher lifecycle than operational state.



---

## 30. Complete NVMe/NAND example

The example below intentionally uses only Simple-style indentation blocks for lifecycle declarations.

### 30.1 Life graph

```simple
life NvmeLife:
    command
    queue_reset survives command
    controller_reset survives queue_reset
    subsystem_reset survives controller_reset
    power_loss survives subsystem_reset
    firmware_activation survives power_loss
    sanitize survives firmware_activation
    factory_service survives sanitize
```

### 30.2 Virtual validity domains

```simple
virtual life SameMedia:
    base: NvmeLife.power_loss
    requires: media_generation_matches
    requires: nand_geometry_matches
    invalidated_by: media_replacement
    invalidated_by: incompatible_geometry
    recover: reconcile_media

virtual life SameHostAssociation:
    base: NvmeLife.controller_reset
    requires: host_identity_matches
    invalidated_by: host_replacement
    invalidated_by: namespace_detach
    recover: reconcile_host
```

### 30.3 Transitions

```simple
transition NvmeControllerReset:
    crosses: NvmeLife.controller_reset
    kind: reset
    volatile: lose
    retained: ControllerRetention
    persistent: preserve_committed
    environment: ControllerResetEnvironment
    restart: ControllerBoot

transition NvmeSuddenPowerLoss:
    crosses: NvmeLife.power_loss
    kind: crash
    volatile: lose
    retained: CapacitorBackedRetention
    persistent: NandMetadataFailure
    environment: may_change
    restart: ControllerBoot

transition NvmeFirmwareActivation:
    crosses: NvmeLife.firmware_activation
    kind: update
    manifest: NvmeFirmwareManifest
    validate: validate_nvme_update
    migrate: migrate_nvme_metadata
    rollback: rollback_nvme_firmware
    restart: BootloaderEntry
```

### 30.4 State representations

```simple
@codec(MappingRootCodec)
struct MappingRoot:
    id: MappingRootId
    sequence: MappingSequence
    root_page: PhysicalPage
    journal_tail: JournalSequence

    invariant:
        sequence >= 0

@codec(NamespaceCodec)
struct NamespaceState:
    id: NamespaceId
    capacity: LbaCount
    mapping_root: EntityRef<MappingRoot>
    mapping_cache: Rebuild<MappingCache>
    io_scheduler: Rebind<IoScheduler>
    host: EnvRef<NvmeHost>
    media: EnvRef<NandMedia>

    invariant:
        capacity > 0
```

### 30.5 Persistent roots

```simple
@section(".persist.mapping_root")
@life(NvmeLife.power_loss)
@identity(stable, MappingRootId)
@recovery(MappingRootRecovery)
var mapping_root_store: PersistentRoot<MappingRoot>

@section(".persist.namespace")
@life(NvmeLife.power_loss)
@identity(stable, NamespaceId)
@recovery(NamespaceRecovery)
var namespace_store: PersistentRoot<NamespaceState>
```

### 30.6 Environment contracts

```simple
@environment
trait NandMedia:
    fn identity() -> MediaIdentity
    fn generation() -> MediaGeneration
    fn geometry() -> NandGeometry
    fn read_page(page: PhysicalPage) -> Result<PageData, NandFault>
    fn program_page(
        page: PhysicalPage,
        data: PageData
    ) -> Result<Unit, NandFault>

@environment
trait NvmeHost:
    fn identity() -> HostIdentity
    fn reset_kind() -> ResetKind
    fn attached_namespaces() -> NamespaceSet
```

### 30.7 Recovery declarations

```simple
recovery MappingRootRecovery for MappingRoot:
    life: NvmeLife.power_loss
    schema: 2
    codec: MappingRootCodec
    decode: decode_mapping_root
    validate: validate_mapping_root
    migrate: migrate_mapping_root
    recover: recover_mapping_root
    clean_start: reconstruct_mapping_root
    reconcile: reconcile_mapping_media
    activate: activate_mapping_root
    restart: MappingRecoveryJournal

    policy:
        choose: automatic
        selector: select_mapping_root
        candidate: latest_complete_root
        candidate: last_known_good_root
        candidate: replay_mapping_journal
        fallback: reconstruct_from_nand
        proof: mapping_selector_safe

    clean:
        preserve: id
        rebuild:
            root_page: full_nand_scan
        reset: journal_tail
        forbid_loss: mapped_user_data
        proof: mapping_reconstruction_safe

recovery NamespaceRecovery for NamespaceState:
    life: NvmeLife.power_loss
    schema: 3
    codec: NamespaceCodec
    decode: decode_namespace
    validate: validate_namespace
    migrate: migrate_namespace
    recover: recover_namespace
    clean_start: clean_namespace
    reconcile: reconcile_namespace
    activate: activate_namespace
    restart: idempotent

    policy:
        choose: automatic
        selector: select_namespace_candidate
        candidate: latest_complete_namespace
        candidate: last_known_good_namespace
        candidate: replay_namespace_journal
        fallback: safe_mode
        proof: namespace_selector_safe

    clean:
        preserve: id
        preserve: capacity
        rebuild:
            mapping_root: resolve_or_rebuild_mapping
        reset: mapping_cache
        forbid_loss: mapped_user_data
        proof: namespace_clean_policy_safe
```

### 30.8 Recovery state machine as normal Simple

```simple
enum MappingRecoveryState:
    Discover
    Candidate(RecoveryCandidate<MappingRoot>)
    Replay(Validated<MappingRoot>, JournalCursor)
    Reconcile(Validated<MappingRoot>)
    Activate(Reconciled<MappingRoot>)
    Ready(Active<MappingRoot>)
    SafeMode(RecoveryFault)

fn recover_mapping_root(
    ctx: &mut MappingRecoveryContext
) -> RecoveryResult<Validated<MappingRoot>>:
    var state = MappingRecoveryState.Discover

    loop:
        match state:
            case MappingRecoveryState.Discover:
                state = discover_mapping_candidate(ctx)

            case MappingRecoveryState.Candidate(candidate):
                state = validate_mapping_candidate(ctx, candidate)

            case MappingRecoveryState.Replay(root, cursor):
                state = replay_mapping_records(ctx, root, cursor)

            case MappingRecoveryState.Reconcile(root):
                state = reconcile_mapping_root(ctx, root)

            case MappingRecoveryState.Activate(root):
                return Ok(root.validated())

            case MappingRecoveryState.Ready(root):
                return Ok(root.validated())

            case MappingRecoveryState.SafeMode(fault):
                return Err(fault)
```

The exact enum matching syntax can follow the current compiler's final canonical pattern; the key design point is that recovery logic remains normal Simple code.

### 30.9 Atomic update

```simple
@power_atomic(MappingJournal)
fn map_lba(
    state: &mut Active<MappingRoot>,
    lba: Lba,
    page: PhysicalPage
) -> Result<Unit, MappingFault>:
    in:
        state.mapping_invariant()
        lba < state.capacity()

    state.update(lba, page)
    MappingJournal.record_mapping(lba, page)

    out(ret):
        ret.is_ok() implies state.mapping_invariant()
```

### 30.10 Rebuild proof target

```simple
@verify
fn mapping_cache_model_valid(
    root: MappingRoot,
    cache: MappingCache
) -> bool:
    out(ret):
        ret implies cache.references(root.sequence)
    ...
```

Handwritten Lean proves rebuilding the cache preserves externally observable mapping behavior.

---

## 31. Bare-metal retained-RAM example

### 31.1 Lifecycle

```simple
life McuLife:
    call
    task survives call
    sleep survives task
    deep_sleep survives sleep
    reset survives deep_sleep
    power_loss survives reset
    firmware_update survives power_loss
```

### 31.2 Transition

```simple
transition DeepSleepWake:
    crosses: McuLife.deep_sleep
    kind: planned
    volatile: DeepSleepMemoryMap
    retained: preserve
    persistent: preserve_committed
    environment: may_change
    restart: ResumeEntry
```

### 31.3 State

```simple
@codec(ResumeCodec)
struct ResumeState:
    sequence: u64
    work_cursor: WorkCursor
    sensor_sample: RecordedInput<SensorSample>
    dma: Rebind<DmaChannel>
    timer: Rebind<Timer>
```

### 31.4 Retained root

```simple
@section(".backup_sram")
@life(McuLife.deep_sleep)
@recovery(ResumeRecovery)
var resume_state: PersistentRoot<ResumeState>
```

### 31.5 Important rule

Even though bytes remain in backup SRAM, `dma` and `timer` are rebound. The retained root is validated with a sequence/checksum before use. Startup never treats retained bytes as already-active object state.

---

## 32. Application hot-reload example

```simple
life AppLife:
    request
    worker_restart survives request
    process_restart survives worker_restart
    service_reload survives process_restart
    host_reboot survives service_reload
```

```simple
@codec(SessionCodec)
struct SessionState:
    id: SessionId
    user: UserId
    cart: EntityRef<Cart>
    renderer: Rebind<Renderer>
    socket: EnvRef<ClientConnection>
```

```simple
recovery SessionRecovery for SessionState:
    life: AppLife.service_reload
    schema: 4
    codec: SessionCodec
    decode: decode_session
    validate: validate_session
    migrate: migrate_session
    recover: recover_session
    clean_start: new_session
    reconcile: reconcile_client
    activate: activate_session

    policy:
        choose: automatic
        selector: select_session
        candidate: latest_complete
        candidate: replicated_copy
        fallback: new_session
```

A socket is not serialized as a file descriptor. It is an environment relationship that may be re-established or rejected.

---

## 33. Hibernation example

```simple
@codec(SystemSnapshotCodec)
struct SystemSnapshot:
    firmware: FirmwareIdentity
    hardware: HardwareFingerprint
    schema: SnapshotSchema
    memory_image: SnapshotPages
    device_resume: DeviceResumeCatalog
    consumed: bool
```

```simple
transition LaptopHibernate:
    crosses: DeviceLife.cold_boot
    kind: planned
    prepare: freeze_userspace_and_devices
    snapshot: SystemSnapshot
    validate: validate_system_snapshot
    restore: restore_system_snapshot
    rebind: resume_and_rebind_devices
    fallback: normal_cold_boot
```

Requirements:

- snapshot sealing is atomic;
- incompatible hardware rejects the snapshot;
- external devices are rebound;
- a consumed-image rule prevents unintended replay;
- normal cold boot remains available.

---

## 34. Lifecycle-aware memory-section example

Source:

```simple
@section(".retain.resume")
@life(McuLife.deep_sleep)
@recovery(ResumeRecovery)
var resume_root: PersistentRoot<ResumeState>

@section(".persist.config")
@life(McuLife.firmware_update)
@recovery(ConfigRecovery)
var config_root: PersistentRoot<DeviceConfig>
```

Board SDN:

```sdn
memory:
    backup_sram:
        origin: 0x40024000
        length: 4K
        permissions: rw
        life: deep_sleep
        retention: backup_power_valid

    config_flash:
        origin: 0x080C0000
        length: 64K
        permissions: rw
        life: firmware_update
        write_atomic: 8
        erase_unit: 2048
        tear_model: prefix_or_none

sections:
    .retain.resume:
        memory: backup_sram
        life: deep_sleep
        initialize: retain_and_validate
        zero: never

    .persist.config:
        memory: config_flash
        life: firmware_update
        initialize: recover
        zero: never
```

---

## 35. User-facing design choices

### 35.1 Lifecycle shape

| Option | Strength | Weakness | Decision |
|---|---|---|---|
| Fixed integer levels | trivial checker | cannot represent branches or virtual validity | reject |
| Named total order | readable | still too rigid | support as a simple DAG case |
| Named partial order/DAG | expressive and verifiable | slightly more compiler work | **recommended** |

### 35.2 Source syntax

| Option | Decision |
|---|---|
| Brace block | reject |
| Attribute-only lifecycle | insufficient for declaring graph and transitions |
| Colon/indent declarations plus attributes | **recommended** |
| Large dedicated state-machine DSL | defer; use normal Simple enums/functions |

### 35.3 Field policy syntax

| Option | Decision |
|---|---|
| Prefix field attributes immediately | parser/AST work and current ambiguity |
| Wrapper types only forever | safe but can become verbose |
| Wrapper types as core, field attributes as later sugar | **recommended** |

### 35.4 Persistent identity

| Option | Decision |
|---|---|
| Serialize raw pointer | reject |
| Serialize current `+T` | reject by default |
| Stable `EntityId<T>` and `EntityRef<T>` | **recommended** |
| Preserve `+T` in retained pool | proof-backed exceptional mode |

### 35.5 Recovery notation

| Option | Decision |
|---|---|
| Only callbacks | too little structure for compiler/proofs |
| Full recovery DSL | duplicates Simple and debugger |
| Metadata declaration binding normal functions | **recommended** |
| Declarative policy plus ordinary state machine | **recommended** |

### 35.6 Persistence mechanism

| Context | Recommended mechanism |
|---|---|
| small config/root | double buffer or copy-on-write root |
| NVMe/NAND metadata | journal plus copy-on-write/atomic root |
| persistent memory | typed ordering/transaction substrate |
| intermittent MCU tasks | task atomicity or undo logging |
| planned hibernate | validated snapshot |
| distributed entity | quorum/versioned replication |

Use a hybrid language contract with selectable backend.

### 35.7 Verification approach

| Option | Decision |
|---|---|
| lint only | insufficient |
| Lean only from day one | slow feedback and large initial framework |
| model checker only | bounded, not a proof |
| bounded explorer plus Lean plus refinement | **recommended** |

### 35.8 Strictness integration

| Profile | Recommended behavior |
|---|---|
| moderate | warnings and runtime guards |
| strict | unsafe references/recovery gaps are errors |
| robust | complete life checks and proof status required |
| critical | discharged proofs and release manifest required |

### 35.9 Automatic recovery

| Option | Decision |
|---|---|
| always newest sequence | unsafe when incompatible/corrupt |
| first valid candidate in declared order | safe and predictable |
| proof-constrained selector | **recommended** |
| operator/host choice | supported, still validation-constrained |

### 35.10 Recommended final selection

Adopt:

```text
named lifecycle DAG
colon/indent declarations
wrapper types as canonical field policy
stable EntityRef separate from +T
recovery metadata + ordinary Simple state machine
hybrid persistence backends
post-weave MIR model
bounded crash explorer + Lean
robust/critical enforcement
```

---

## 36. Implementation plan

### Phase 0 — terminology and semantic freeze

Deliver:

- glossary;
- relation direction;
- life/boundary/storage/identity distinction;
- standard result states;
- stable diagnostic IDs;
- feature-gated syntax examples.

Gate:

- no unresolved meaning of “higher life”;
- no syntax example using a brace lifecycle block.

### Phase 1 — parser and lifecycle graph

Implement:

- contextual `life`;
- contextual `virtual life`;
- AST;
- symbol resolution and qualification;
- DAG/cycle checking;
- `@life` attribute;
- graph artifact/IDE view.

Tests:

- parser;
- ambiguous imports;
- cycles;
- DAG branches;
- virtual base resolution.

### Phase 2 — wrappers and dependency checker

Implement:

- `EntityId<T>`;
- `EntityRef<T>`;
- `Rebuild<T>`;
- `Rebind<T>`;
- `EnvRef<T>`;
- `WeakEntityRef<T>`;
- strong-reference graph;
- current pointer/handle rejection;
- diagnostics with shortest path.

Also strengthen `+T` with pool epoch and wrap policy.

### Phase 3 — transition and section model

Implement:

- `transition`;
- board SDN lifecycle fields;
- region/section cross-checks;
- generated retain/validate/recovery tables;
- linker assertions;
- boot-phase catalog.

### Phase 4 — recovery declaration and codec contract

Implement:

- `recovery ... for ...:`;
- schema/type IDs;
- function signature checking;
- policy and clean blocks;
- generated recovery manifest;
- candidate typestates;
- migration-gap checker.

### Phase 5 — persistence runtime

Implement minimum backends:

1. host file-backed store;
2. retained RAM;
3. NOR/flash double buffer;
4. append journal;
5. no-allocation bare-metal variant.

Then add NVMe/NAND and persistent-memory backends.

### Phase 6 — effects and AOP hardening

Implement:

- MIR persistence effects;
- generated AOP rules;
- crash-point instrumentation;
- post-weave certificate;
- strict/robust/critical severity mapping.

### Phase 7 — crash explorer

Implement:

- event trace;
- deterministic power-cut replay;
- bounded torn-write models;
- crash during recovery;
- environment mutation;
- model/result comparison;
- SSpec report generation.

### Phase 8 — Lean generation

Generate:

- life graph;
- entity/reference model;
- transition relations;
- candidate policy;
- section/storage assumptions;
- theorem skeletons;
- stable generated contract.

Handwritten theorem focus:

- dependency safety;
- codec/migration;
- selected-candidate safety;
- recovery restart safety;
- transient non-necessity;
- clean-start policy.

### Phase 9 — MIR refinement

Prove or mechanically check:

- each persistence MIR event maps to the abstract model;
- AOP weaving preserves declared event semantics;
- backend calls refine storage primitives;
- generated trace IDs match test and proof artifacts.

### Phase 10 — bootloader and product integration

Integrate:

- Simple OS boot;
- firmware update/rollback;
- NVMe emulator;
- QEMU;
- target boards;
- hardware power-cut tests;
- release evidence.

---

## 37. Parallel development workstreams

### Workstream A — grammar and parser

Owns:

- contextual declarations;
- AST;
- formatter;
- syntax guide;
- parser SSpecs.

Interface output:

```text
Lifecycle AST schema
```

### Workstream B — semantic/type checker

Owns:

- life graph;
- reference-edge classification;
- wrapper semantics;
- diagnostics;
- strictness integration.

Interface output:

```text
Normalized Lifecycle HIR
```

### Workstream C — handle/entity runtime

Owns:

- pool epoch/generation;
- stable entity IDs;
- resolver;
- activated pools;
- no-allocation variants.

Interface output:

```text
Entity and runtime-handle ABI
```

### Workstream D — persistence backends

Owns:

- store traits;
- double buffer;
- journal;
- retained RAM;
- flash/NAND/block/PMEM implementations.

Interface output:

```text
PersistentStore event contract
```

### Workstream E — boot/linker

Owns:

- SDN schema;
- linker sections;
- startup tables;
- recovery catalog;
- firmware update handoff.

Interface output:

```text
Section/transition manifest
```

### Workstream F — recovery framework

Owns:

- recovery declaration checker;
- candidates;
- policy selector;
- migration;
- clean-start accounting;
- environment reconciliation.

Interface output:

```text
Recovery Manifest and Result ABI
```

### Workstream G — formal verification

Owns:

- Lean semantics;
- generation;
- manual theorem layer;
- assumptions registry;
- proof gates.

Interface output:

```text
Generated Lean contract
```

### Workstream H — fault testing and observability

Owns:

- crash-point IDs;
- simulator;
- QEMU/HIL injection;
- SSpec reports;
- trace decoder.

Interface output:

```text
Persistence event and evidence format
```

Workstreams must agree early on stable IDs for lifecycle levels, storage events, entity types, record schemas, transitions, and proof obligations.

---

## 38. Acceptance criteria

### Language

- all lifecycle declarations use colon/indent syntax;
- parser/formatter round trip;
- graph permits branches and rejects cycles;
- qualified and unqualified names behave deterministically.

### Type safety

- no persistent raw pointer/runtime handle without an explicit proof-backed exception;
- strong dependency direction is checked transitively;
- shorter-lived resources require rebuild/rebind/environment wrappers;
- generation/epoch stale-handle tests pass.

### Persistence

- every durable entity has schema, codec, validation, migration policy, recovery, clean start, reconciliation, and activation;
- incomplete writes are represented by the backend model;
- recovery can be interrupted and restarted;
- clean start cannot silently lose protected state.

### Boot/linker

- section durability is checked against entity life;
- retained sections are not accidentally zeroed;
- recovery entry points and metadata are present in the boot image;
- update compatibility and rollback are checked before activation.

### Verification

- generated life graph and recovery model compile in Lean;
- critical proofs contain no `sorry`;
- trusted assumptions are enumerated;
- post-weave fingerprint matches executable artifacts;
- non-persistence proofs exist for declared critical `Rebuild` state.

### Testing

- crash after every persistent event;
- crash during recovery;
- malformed records;
- environment changes;
- migration chains;
- real journal/codec path in system tests;
- QEMU and at least one target-board evidence lane.

---

## 39. RAG assessment of current Simple readiness

| Area | Status | Reason |
|---|---|---|
| Colon/indent grammar | Green | canonical language form already exists |
| Prefix attributes | Green | current parser and low-level attributes provide the pattern |
| `@section` and linker SDN | Green/Amber | strong design foundation; lifecycle fields still needed |
| Runtime handles | Amber | generation concept exists; cross-boot identity/epoch is missing |
| Strictness profiles | Green | robust/critical integration point exists |
| AOP | Amber | pointcuts/weaving exist but feature is still in progress and proof integration must be hardened |
| Function contracts | Green/Amber | useful current syntax; verification subset is bounded |
| Generated Lean workflow | Amber | active foundation; crash semantics/refinement not yet present |
| Generic serialization | Amber/Red | serializers exist, but no authoritative crash-safe persistence contract |
| Lifecycle DAG | Red | new |
| Stable persistent entity references | Red | new |
| Transition/storage failure model | Red | new |
| Recovery declaration/policy | Red | new |
| Recovery-during-recovery proof | Red | new |
| Section lifecycle validation | Red | new |
| Crash explorer/HIL evidence | Red | new |

The project has enough foundations to implement this incrementally, but it should not claim complete lifecycle or power-failure verification until the red items and refinement gates are complete.

---

## 40. Final recommended grammar surface

```simple
life DeviceLife:
    call
    task survives call
    process survives task
    service_restart survives process
    warm_boot survives service_restart
    cold_boot survives warm_boot
    power_loss survives cold_boot
    firmware_update survives power_loss
    factory_reset survives firmware_update

virtual life SameHardware:
    base: DeviceLife.cold_boot
    requires: hardware_fingerprint_matches
    invalidated_by: hardware_replacement
    recover: reject_or_cold_boot

transition SuddenPowerLoss:
    crosses: DeviceLife.power_loss
    kind: crash
    volatile: lose
    retained: PlatformRetention
    persistent: PlatformStorageFailure
    environment: may_change
    restart: ResetVector

@codec(AppCodec)
struct AppState:
    id: AppId
    document: EntityRef<Document>
    cache: Rebuild<AppCache>
    renderer: Rebind<Renderer>
    display: EnvRef<Display>

@section(".persist.app")
@life(DeviceLife.power_loss)
@identity(stable, AppId)
@recovery(AppRecovery)
var app_root: PersistentRoot<AppState>

recovery AppRecovery for AppState:
    life: DeviceLife.power_loss
    schema: 2
    codec: AppCodec
    decode: decode_app
    validate: validate_app
    migrate: migrate_app
    recover: recover_app
    clean_start: clean_app
    reconcile: reconcile_app
    activate: activate_app
    restart: idempotent

    policy:
        choose: automatic
        selector: select_app_candidate
        candidate: latest_complete
        candidate: last_known_good
        candidate: replay_committed
        fallback: safe_mode
        proof: app_selector_safe

    clean:
        preserve: id
        rebuild:
            document: recover_document
        reset: cache
        forbid_loss: user_document
        proof: app_clean_policy_safe

@power_atomic(AppJournal)
fn update_document(
    state: &mut Active<AppState>,
    change: DocumentChange
) -> Result<Unit, UpdateFault>:
    in:
        state.valid()

    state.document.apply(change)
    AppJournal.record(change)

    out(ret):
        ret.is_ok() implies state.valid()
```

This surface is small enough to fit Simple, rich enough to describe the requested system, and structured enough to generate static checks, runtime metadata, system tests, and Lean proof obligations.

---

## 41. Conclusions

1. Lifecycle must be a named partial order, not a fixed number or a synonym for memory placement.
2. Simple's canonical colon-and-indentation grammar should be used throughout lifecycle declarations.
3. `struct` remains the data language; lifecycle management wraps authoritative roots/entities.
4. Runtime `+T` handles and persistent `EntityRef<T>` serve different purposes and must never be conflated.
5. Serialization is only the first stage. Validation, migration, recovery, clean start, reconciliation, and activation are separate contracts.
6. Crash recovery, hibernation, intermittent execution, and firmware update share lifecycle types but use different persistence strategies.
7. Long-lived roots should depend on stateless service contracts, stable entities, or explicit rebind capabilities.
8. Physical memory durability belongs in linker/board SDN and is cross-checked against source lifecycle intent.
9. Recovery must remain safe when power fails during recovery itself.
10. AOP is useful for hardening and fault injection, but proof semantics must target the post-weaving IR.
11. Lean should prove graph safety, codec/migration laws, recovery soundness, transient-state non-necessity, and refinement under explicit assumptions.
12. A bounded crash explorer and real system-level power-cut tests are required even when formal proofs exist.
13. `robust` should make lifecycle violations compile errors; `critical` should additionally require discharged proof and release evidence.
14. The most practical implementation path is wrappers first, field-attribute sugar later.
15. The proposed integration is sufficiently distinct to justify a dedicated language/systems research track.

---

## 42. Research and repository references

### 42.1 Simple repository sources

1. Simple syntax quick reference:  
   <https://github.com/ormastes/simple/blob/main/doc/07_guide/quick_reference/syntax_quick_reference.md>

2. Rust parser token definitions:  
   <https://github.com/ormastes/simple/blob/main/src/compiler_rust/parser/src/token.rs>

3. Parser item dispatch and block handling:  
   <https://github.com/ormastes/simple/blob/main/src/compiler_rust/parser/src/parser_impl/core.rs>

4. Attribute parser:  
   <https://github.com/ormastes/simple/blob/main/src/compiler_rust/parser/src/parser_impl/attributes.rs>

5. Attribute syntax example:  
   <https://github.com/ormastes/simple/blob/main/examples/02_language_features/syntax/attribute_syntax.spl>

6. Current struct parser:  
   <https://github.com/ormastes/simple/blob/main/src/compiler_rust/parser/src/types_def/mod.rs>

7. Current contracts parser:  
   <https://github.com/ormastes/simple/blob/main/src/compiler_rust/parser/src/stmt_parsing/contract.rs>

8. Memory design and `handle_pool`:  
   <https://github.com/ormastes/simple/blob/main/doc/05_design/language/misc/memory.md>

9. Handle pointer specification:  
   <https://github.com/ormastes/simple/blob/main/doc/06_spec/03_system/feature/usage/handle_pointers_spec.md>

10. Current handle implementation:  
    <https://github.com/ormastes/simple/blob/main/src/lib/nogc_sync_mut/ptr/handle.spl>

11. Linker-script generation design:  
    <https://github.com/ormastes/simple/blob/main/doc/05_design/compiler/architecture/linker_script_gen_design.md>

12. Cortex-M33 `@section` and `@align` usage:  
    <https://github.com/ormastes/simple/blob/main/src/os/kernel/arch/cortex_m33/boot.spl>

13. AOP specification:  
    <https://github.com/ormastes/simple/blob/main/doc/06_spec/feature/usage/aop_spec.md>

14. Lean verification with AOP design:  
    <https://github.com/ormastes/simple/blob/main/doc/01_research/infra/aop/lean_verification_with_aop.md>

15. Strictness tiers:  
    <https://github.com/ormastes/simple/blob/main/doc/07_guide/language/strictness_tiers.md>

16. Lean verification workflow:  
    <https://github.com/ormastes/simple/blob/main/doc/07_guide/compiler/lean_verification_workflow.md>

17. Memory capabilities verification specification:  
    <https://github.com/ormastes/simple/blob/main/doc/06_spec/00_formal_verification/compiler/memory_capabilities_spec.md>

### 42.2 Typestate, ownership, regions, and capabilities

18. Robert E. Strom and Shaula Yemini, “Typestate: A Programming Language Concept for Enhancing Software Reliability,” 1986:  
    <https://research.ibm.com/publications/typestate-a-programming-language-concept-for-enhancing-software-reliability>

19. Manuel Fähndrich and Robert DeLine, “Adoption and Focus: Practical Linear Types for Imperative Programming,” PLDI 2002:  
    <https://www.microsoft.com/en-us/research/publication/adoption-and-focus-practical-linear-types-for-imperative-programming/>

20. Mads Tofte and Jean-Pierre Talpin, “Implementation of the Typed Call-by-Value Lambda Calculus Using a Stack of Regions,” POPL 1994:  
    <https://doi.org/10.1145/174675.177855>

21. Mads Tofte and Jean-Pierre Talpin, “Region-Based Memory Management,” 1997:  
    <https://doi.org/10.1006/inco.1996.2613>

22. David Walker, Karl Crary, and Greg Morrisett, “Typed Memory Management in a Calculus of Capabilities”:  
    <https://www.cs.cmu.edu/~dpw/papers/capabilities-abstract.html>

### 42.3 Crash safety and verified recovery

23. Haogang Chen et al., “Using Crash Hoare Logic for Certifying the FSCQ File System,” SOSP 2015:  
    <https://doi.org/10.1145/2815400.2815402>

24. FSCQ project:  
    <https://css.csail.mit.edu/fscq/>

25. Tej Chajed et al., “Verifying Concurrent, Crash-Safe Systems with Perennial,” OSDI 2020:  
    <https://www.usenix.org/conference/osdi20/presentation/chajed>

26. Tej Chajed et al., “GoJournal: a Verified, Concurrent, Crash-Safe Journaling System,” OSDI 2021:  
    <https://www.usenix.org/conference/osdi21/presentation/chajed>

27. Tej Chajed et al., “Verifying the DaisyNFS Concurrent and Crash-Safe File System with Sequential Reasoning,” OSDI 2022:  
    <https://www.usenix.org/conference/osdi22/presentation/chajed>

28. Tej Chajed et al., “Argosy: Verifying Layered Storage Systems with Recovery Refinement,” PLDI 2019:  
    <https://pldi19.sigplan.org/details/pldi-2019-papers/33/Argosy-Verifying-Layered-Storage-Systems-with-Recovery-Refinement>

29. Hayley LeBlanc et al., “SquirrelFS: Using the Rust Compiler to Check File-System Crash Consistency,” OSDI 2024:  
    <https://www.usenix.org/conference/osdi24/presentation/leblanc>

### 42.4 Intermittent computing

30. Brandon Lucia and Benjamin Ransford, “A Simpler, Safer Programming and Execution Model for Intermittent Systems,” PLDI 2015, DINO:  
    <https://doi.org/10.1145/2737924.2737978>

31. Kiwan Maeng, Alexei Colin, and Brandon Lucia, “Alpaca: Intermittent Execution without Checkpoints”:  
    <https://doi.org/10.1145/3133920>

32. Alexei Colin and Brandon Lucia, “Chain: Tasks and Channels for Reliable Intermittent Programs”:  
    <https://doi.org/10.1145/3022671.2983995>

33. Milijana Surbatovich, Brandon Lucia, and Limin Jia, “Towards a Formal Foundation of Intermittent Computing,” OOPSLA 2020:  
    <https://doi.org/10.1145/3428231>

34. Yilun Wu et al., “IntOS: Persistent Embedded Operating System and Language Support for Multi-threaded Intermittent Computing,” OSDI 2024:  
    <https://www.usenix.org/conference/osdi24/presentation/wu-yilun>

### 42.5 Persistent memory and stable references

35. PMDK `libpmemobj` documentation:  
    <https://pmem.io/pmdk/manpages/linux/v1.2/libpmemobj.3/>

36. PMDK persistent object identifier documentation:  
    <https://pmem.io/pmdk/manpages/windows/v1.4/libpmemobj/oid_is_null.3/>

37. PMDK transaction documentation:  
    <https://pmem.io/pmdk/manpages/linux/v1.4/libpmemobj/pmemobj_tx_begin.3/>

### 42.6 Power management, boot, and update

38. Linux kernel, “Swap suspend”:  
    <https://www.kernel.org/doc/html/latest/power/swsusp.html>

39. Linux kernel, system sleep and hibernation documentation:  
    <https://docs.kernel.org/admin-guide/pm/sleep-states.html>

40. Linux kernel, Hyper-V hibernation and device rebinding example:  
    <https://docs.kernel.org/virt/hyperv/hibernation.html>

41. MCUboot design:  
    <https://docs.mcuboot.com/design.html>

42. RFC 9019, “A Firmware Update Architecture for Internet of Things”:  
    <https://www.rfc-editor.org/rfc/rfc9019.html>

43. RFC 9124, “A Manifest Information Model for Firmware Updates in Internet of Things Devices”:  
    <https://www.rfc-editor.org/rfc/rfc9124.html>

### 42.7 OS state management and formal verification infrastructure

44. Kevin Boos et al., “Theseus: an Experiment in Operating System Structure and State Management,” OSDI 2020:  
    <https://www.usenix.org/conference/osdi20/presentation/boos>

45. Gerwin Klein et al., “seL4: Formal Verification of an OS Kernel”:  
    <https://doi.org/10.1145/1629575.1629596>

46. Theorem Proving in Lean 4:  
    <https://lean-lang.org/theorem_proving_in_lean4/>

47. Aeneas verification project:  
    <https://aeneasverif.github.io/>

48. RustBelt project:  
    <https://plv.mpi-sws.org/rustbelt/>

---

## Appendix A. Normative lifecycle rules

1. `X survives Y` adds `Y <= X`.
2. Life graphs are finite and acyclic.
3. Strong stored references require owner life `<=` dependency life.
4. Persistent encodings contain no runtime address or runtime handle by default.
5. Every stable reference is resolved and validated after a transition that invalidates runtime identity.
6. Decoded data is not active.
7. Every persistent entity has an explicit schema and recovery registration.
8. Recovery is safe when interrupted.
9. Clean start accounts for every authoritative field.
10. `forbid_loss` state is unreachable from destructive fallback unless authenticated destructive policy explicitly permits it.
11. Environment observations are reconciled, not blindly restored.
12. Source life cannot exceed physical region durability.
13. Startup does not zero or overwrite retained/persistent sections contrary to section policy.
14. AOP-transformed code is verified after weaving.
15. `critical` claims enumerate assumptions and contain no admitted proof.

## Appendix B. Minimal first milestone

The smallest useful vertical slice is:

1. `life` declaration;
2. `@life`;
3. `EntityRef<T>`, `Rebuild<T>`, `Rebind<T>`, and `EnvRef<T>`;
4. strong dependency lint;
5. stable-ID host file store;
6. `recovery` declaration with codec/validate/recover/clean;
7. double-buffer backend;
8. power cut after every write/commit step;
9. generated lifecycle graph and one Lean dependency theorem;
10. QEMU or host system test using the real codec and recovery implementation.

This slice is already useful and does not require solving the complete compiler-refinement proof first.

## Appendix C. Terms to avoid

Avoid using one word to mean multiple dimensions:

| Avoid ambiguous phrase | Use instead |
|---|---|
| persistent object | durable entity, persistent record, or active entity |
| object lifetime | execution lifetime or lifecycle domain |
| valid after boot | decoded, validated, reconciled, or active |
| pointer survives | stable entity ID resolves after transition |
| save state | snapshot, journal commit, encode record, or retain RAM |
| recover | replay, rollback, reconstruct, reconcile, activate, or safe mode |
| reset everything | explicit clean-start field policy |
| fully verified | state exact proof level, assumptions, admits, and trusted code |
