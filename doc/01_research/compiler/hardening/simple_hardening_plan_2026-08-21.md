# Simple Hardening Plan

## Critical-profile type safety, static/complete/dynamic completeness, verified dynload, aspect sealing, compiler path coverage, and parallel implementation plan

**Date:** 2026-08-21  
**Repository:** [`ormastes/simple`](https://github.com/ormastes/simple)  
**Repository revision inspected:** `d200f577aaad0b28995c857c1df4887a1784d033` (`main` at the time of inspection)  
**Status:** Final architecture and staged implementation plan; source-inspection based. No fresh bootstrap or test suite was executed for this report.

**Companion documents (added 2026-08-21):**
- Design: `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md`
- Plan: `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`

---

## 1. Executive decision

Simple should harden around five non-negotiable rules:

1. **The safe critical subset contains no `Any`.**  
   In `critical`, `Any` may appear only inside a capability-scoped `unsafe` representation boundary. An `Any` value must be checked and converted to a monomorphized generic, a closed sum type, a typed interface object, or a validated opaque representation before it can leave that boundary.

2. **Static extensibility and dynamic linkage are different axes.**  
   Simple should support three semantic completeness states:
   - **`static`** — the constructor/operation universe is closed at source/compiler build time.
   - **`complete`** — modules may be independently compiled or dynloaded, but the selected universe is frozen, verified, and assigned a deterministic seal before execution.
   - **`dyn`** — the universe remains open after execution starts and therefore cannot provide whole-world exhaustiveness.

   Separately, an implementation may be **statically linked** or **dynloaded**. A dynloaded module can still be semantically `complete`.

3. **Compiler completeness is a pipeline invariant, not a test accident.**  
   Every grammar production, token class, FlatAst tag, AST variant, HIR variant, MIR operation, interpreter operation, and backend operation must be accounted for as:
   - `Implemented`
   - `Normalized(target)`
   - `Unsupported(reason)`
   - `NotApplicable(reason)`

   An absent entry is a build error. Silent conversion to `NilLit`, `Error`, zero, an empty block, a scalar fallback, or a no-op is forbidden.

4. **Generics in critical/native builds are monomorphized, not erased to `Any`.**  
   The monomorphization pass must use typed tables and a deterministic fixed-point worklist. After its post-pass verifier, no unresolved type parameter, generic call, erased generic payload, or generic-layout placeholder may reach canonical MIR.

5. **Aspects and dynloaded compiler extensions are verified before they affect semantics.**  
   A critical build uses only `static` and sealed `complete` aspects/extensions. The chosen weave plan, capability set, effects, handlers, ABI hashes, dependency graph, and proof/evidence hashes become part of the completeness seal and artifact identity. Open `dyn` advice or semantic extension after the seal is prohibited.

The resulting critical pipeline is:

```text
source/config
  -> grammar + representation validation
  -> FlatAst/AST total-transition validation
  -> HIR lowering
  -> type/effect/ownership/safety checking
  -> select + verify complete modules/aspects
  -> typed HIR weaving/normalization
  -> repeat type/effect/safety checks
  -> monomorphization fixed point
  -> post-mono closed-world verifier
  -> canonical HIR/MIR lowering
  -> MIR completeness + safety verifier
  -> interpreter/JIT/native differential validation
  -> backend coverage verification
  -> reproducible artifact + completeness seal + evidence manifest
```

---

## 2. Goals and non-goals

### 2.1 Goals

This plan is designed to make the following claims executable:

- Adding a static enum/IR variant cannot silently bypass an existing match.
- Selecting a dynloaded but `complete` module cannot leave an operation handler missing.
- A parser cannot produce a node that the next compiler stage silently discards.
- `Any` cannot cross a critical safe boundary.
- Generic code cannot reach native codegen with unresolved type representation.
- An aspect cannot modify code after the verified critical world has been sealed.
- The Rust seed and self-hosted Simple compiler cannot silently accept different critical programs.
- Interpreter, JIT, LLVM/native, and Cranelift/native cannot silently assign different semantics to the same accepted critical program.
- A release gate cannot report “complete” from prose, TODO state, or a non-executed checker.

### 2.2 Non-goals

The plan does not require:

- converting every optional module into a core static enum variant;
- forbidding dynamic plugins in non-critical profiles;
- using `Any` nowhere in all Simple programs;
- forcing all compiler metadata inline into AST/HIR nodes;
- hot-unloading semantic compiler extensions in critical mode;
- claiming zero overhead for transparent runtime advice;
- immediately proving every compiler pass in Lean before basic fail-closed coverage exists.

---

## 3. Repository ground truth and hardening drivers

The repository already contains important foundations, but source inspection shows that several completeness claims are not yet backed by executable invariants.

### 3.1 Existing strengths

The current tree includes:

- a named `critical` assurance profile and fail-closed requirements;
- typed profile resolution and project pinning;
- a safety checker integrated into a driver pass with profile-aware severity;
- HIR match-coverage records keyed by resolved enum/variant IDs;
- loud errors for several unsupported generic native paths;
- a monomorphization phase positioned between HIR and MIR;
- aspect-pack catalog/container/routed-load infrastructure;
- explicit aspect activation modes and ABI checking in the implemented loader slice;
- existing bug documents that record silent fallback classes instead of hiding them;
- a parallel-agent ownership discipline and release-evidence model.

These should be retained and made authoritative rather than replaced.

### 3.2 Confirmed gaps that this plan addresses

| Area | Current source/repository evidence | Hardening consequence |
|---|---|---|
| Match coverage | `ResolvedMatchCoverage.is_exhaustive()` currently treats a wildcard as exhaustive. | In critical compiler IR, `_` cannot satisfy closed static or frozen-complete coverage. |
| FlatAst bridge | The documented `spawn`/`await`/`yield` failure class silently became `NilLit` before loud fallback and real mappings were added. | Bridge mappings must be generated total relations with no semantic default. |
| HIR→MIR type coverage | An open bug report records 9 of 26 `HirTypeKind` variants falling into one fatal wildcard. | Every type variant needs an explicit lowering/normalization/unsupported decision. |
| Type checking | The HIR typecheck pass is wired, but the current source comments state its default remains advisory until a census is complete. | Critical must always use deny severity; release evidence must prove the pass executed. |
| Safety checking | The current safety pass is wired, but it still contains wildcard/pass patterns in traversal and duplicate name-based operation lists. | Generate exhaustive visitors and canonical unsafe-operation capabilities. |
| `Any` representation | The repository records interpreter/JIT/native divergence, incorrect boxing, and still-open consumer-side `.to_text()` / comparison issues. | `Any` is unsafe-only in critical; compiler internals migrate away from erased storage. |
| Monomorphization | Current source still stores generic definitions/specializations as `Any`; specialization copies functions unchanged; module rewrite is a no-op; type substitution is identity/error fallback. | Keep native generic gates fail-closed until typed mono and post-pass verification pass. |
| Aspect dynload | Container/catalog routing and some ABI checks exist; typed facet grammar/HIR, complete binding proof, atomic generation publication, signature policy, and post-weave verification are partial/missing. | Separate loader readiness from semantic completeness; critical accepts only sealed complete aspects. |
| Bootstrap parity | Multiple bug reports show defects visible only in one stage/engine. | Add generated parity manifests and differential source fixtures to every bootstrap gate. |

### 3.3 The central diagnosis

The recurring defect pattern is not “HIR is unfinished because critical mode was off.” It is:

```text
a known producer universe
  + an independently maintained consumer dispatch
  + a generic fallback or erased representation
  + incomplete execution-matrix coverage
  = a missing semantic path that can survive ordinary builds
```

Critical mode should make such gaps fatal, but ordinary compiler construction should already prevent structural omissions.

---

## 4. Research conclusions adopted for Simple

This design combines several established techniques rather than copying one system wholesale.

### 4.1 Closed algebraic data types and exhaustive matching

Closed enums provide the strongest structural completeness and cheapest dispatch. Rust’s ordinary enums are nominal disjoint unions; external `non_exhaustive` enums require a wildcard and deliberately weaken downstream exhaustiveness. Simple should keep the core compiler IR closed and should not model all extensibility as `non_exhaustive`.

**Adopt:**
- closed static constructor sets;
- exhaustive matches;
- explicit discriminants and invalid-discriminant rejection;
- sum types instead of unbounded dynamic typing when alternatives are finite.

**Reject:**
- `_` as a normal compiler-IR compatibility mechanism.

### 4.2 Trees That Grow

GHC’s “Trees That Grow” work addresses compiler AST extension and decoration without proliferating incompatible tree definitions.

**Adopt:**
- typed extension slots for pass-specific annotations;
- zero/default extension records in configurations that do not need the data;
- structural variants only for genuinely different syntax/semantics.

**Consequence for Simple:**

```text
new syntax/semantic form       -> static/complete/dyn variant
extra data about existing form -> typed extension slot or side table
backend-only data              -> backend dialect/side table
sparse analysis result         -> NodeId-indexed side table
```

This reduces the number of places where exhaustiveness can break.

### 4.3 MLIR dialects, operation interfaces, and verifiers

MLIR shows how an open IR can remain analyzable: operations are namespaced, interfaces state required semantic operations, promised interfaces fail when not registered, and operation verifiers validate dynamic definitions.

**Adopt:**
- namespaced extension identity;
- required operation/type/dialect interfaces;
- “promised handler” declarations that become load/seal errors when missing;
- a verifier for every dynamic constructor schema;
- generated declarative descriptors rather than string comparisons scattered across passes.

### 4.4 Rust `Any`, checked downcast, and unsafe obligations

Rust’s `Any` provides runtime type identification and checked downcasts; unchecked downcasts are unsafe because a wrong asserted type is undefined behavior.

**Adopt more strictly in critical Simple:**
- raw `Any` is a representation escape;
- the escape is permitted only in an explicitly capability-scoped unsafe block;
- conversion out is checked and total (`Result`/sum), not an unchecked cast;
- values do not escape the block in erased form.

### 4.5 Rust monomorphization graph

Rust’s mono-item collector discovers roots and recursively follows uses until the complete code-generation graph is known.

**Adopt:**
- deterministic worklist/fixed-point collection;
- separate semantic specialization identity from target-specific artifact identity;
- root and transitive-use collection;
- post-monomorphization checks;
- recursion and code-size limits;
- deduplication across equal instantiations.

### 4.6 SPARK representation boundaries

SPARK allows restricted unchecked conversions but imposes legality, size, alignment, suitability, and validity conditions. It treats invalid external data as a proof hazard.

**Adopt:**
- representation-boundary declarations;
- same-size/alignment/schema checks;
- `PotentiallyInvalid`-like taint until validation;
- no proof claim over unchecked data before validation.

### 4.7 eBPF verifier-gated dynamic loading

eBPF demonstrates that dynamically supplied code can be admitted only after a verifier establishes acceptable state and path properties.

**Adopt:**
- module admission before activation;
- typed verifier receipts;
- no “load now, discover missing handler on first execution” in complete or critical modes.

### 4.8 OSGi lazy activation

OSGi separates resolution/start/activation and supports lazy activation.

**Adopt:**
- explicit lifecycle;
- catalog and verification before code activation;
- lazy loading for non-critical or already sealed complete modules;
- deterministic dependency activation.

### 4.9 AspectJ load-time weaving

AspectJ requires all load-time aspects to be known before affected types are loaded to avoid missed invariants.

**Adopt for critical:**
- all semantics-changing aspects are selected before affected HIR/code is sealed;
- no late aspect that could have matched already-compiled code;
- the post-weave program, not the pre-weave program, is verified.

### 4.10 Linux static keys

Linux static keys show that dormant transparent instrumentation can have a very small disabled path through patchable branch sites, but not universally zero cost.

**Adopt:**
- optional patchable advice mode outside critical or when predeclared in a complete seal;
- precise performance claims by activation mode;
- exact zero business-path overhead only when the aspect is omitted or reached through explicit facet acquisition.

---

## 5. The three semantic completeness states

### 5.1 The states

| State | Universe closes | Extension mechanism | Exhaustiveness point | Critical eligibility | Hot-path dispatch |
|---|---|---|---|---|---|
| `static` | Source/compiler build | Edit defining declaration | Compile time | Yes | direct switch/jump table |
| `complete` | Config/link/seal | Independently built or dynloaded modules selected before seal | Config/link/seal + generated compile check | Yes | dense frozen switch/table |
| `dyn` | Does not close while running | Late runtime registration | Only per-registration contracts; no whole-world proof | No, unless frozen into `complete` first | registry/interface dispatch |

### 5.2 Independent linkage state

Do not encode linkage into the semantic state.

| Semantic state | Statically linked implementation | Dynloaded implementation |
|---|---:|---:|
| `static` | normal | normally not needed |
| `complete` | supported | supported and preferred for modular compiler components |
| `dyn` | supported | supported |

Examples:

```text
hir_gpu.smf:
    linkage = dynloaded
    semantic_state = complete
    activation = startup or lazy-after-seal

ide_probe:
    linkage = dynloaded
    semantic_state = dyn
    activation = manual/first_use
```

A release may statically link `hir_gpu` without changing its persistent complete-extension identity. This avoids build-configuration-dependent serialized IDs.

### 5.3 Independent selection and activation axes

Retain Simple’s broader config axes:

```text
capability: off | auto | on
placement:  static_link | dynload
activation: startup | first_use | command | manual | hotspot
closure:    static | complete | dyn
```

Critical restrictions:

```text
closure:
    static   allowed
    complete allowed after seal
    dyn      rejected or converted to complete before critical execution

activation:
    startup        allowed
    first_use      allowed only when module code/hash was already verified and sealed
    command/manual allowed only before entering critical execution
    hotspot/hot    rejected for semantics-changing modules/aspects
```

---

## 6. Proposed language and grammar design

The syntax should remain small and build on ordinary enum/match syntax.

### 6.1 Closed static enum

```simple
enum BinOp:
    Add
    Sub
    Mul
    Div
```

Every match is exhaustive:

```simple
fn eval(op: BinOp, a: i64, b: i64) -> i64:
    match op:
        case Add: a + b
        case Sub: a - b
        case Mul: a * b
        case Div: a / b
```

Adding `Mod` makes the consumer fail to compile until handled.

### 6.2 Extensible enum declaration

Recommended syntax:

```simple
enum ExprKind:
    Int(i64)
    Call(Expr, [Expr])

    complete:
    dyn:
```

The empty sections declare the accepted extension domains; constructors are declared by extension modules.

```simple
extend ExprKind:
    complete:
        async.Await(Expr)
        gpu.KernelLaunch(KernelAst)

    dyn:
        ide.LiveProbe(ProbePayload)
```

Rules:

- An enum without `complete:` or `dyn:` is closed.
- An enum with `complete:` accepts selected, seal-time extensions.
- An enum with `dyn:` accepts runtime-open extensions.
- A provider must use a globally stable module/constructor identity.
- The original static ordinal sequence is never modified by an extension.
- An extension cannot change the payload schema without an ABI-version change.

### 6.3 Match semantics

```simple
match expr.kind:
    case Int(value):
        lower_int(value)

    case Call(callee, args):
        lower_call(callee, args)

    case complete ext:
        ext.require<HirLower>().lower(self)

    case dyn ext:
        unsupported_dynamic_expr(ext.identity)
```

Meaning:

- `case complete` covers only the frozen complete-extension region.
- It is legal only when the expression binds a verified required interface such as `HirLower`.
- The completeness sealer proves every selected complete constructor implements that interface.
- `case dyn` covers only the open dynamic region.
- Neither arm covers a missing static constructor.
- A new static constructor still makes the match non-exhaustive.
- In critical code, `case dyn` is unreachable by policy and should normally be rejected at seal time.

A compiler pass that requires per-constructor custom code may explicitly list selected complete variants instead:

```simple
match expr.kind:
    case Int(value): ...
    case Call(callee, args): ...
    case async.Await(task): ...
    case gpu.KernelLaunch(kernel): ...
```

The compiler recompiles that consumer against the selected complete-universe manifest. If a new complete constructor is selected, the match fails until updated.

### 6.4 Wildcard policy

`_` remains useful for ordinary application code, but not for closed critical compiler IR.

```simple
@exhaustive
fn lower_expr(expr: HirExpr) -> MirValue:
    match expr.kind:
        ...
        case _: ...  # compile error
```

Diagnostic:

```text
E-COMPLETE-001:
wildcard cannot close an @exhaustive compiler-IR match

static variants must be named explicitly.
use `case complete ext:` only with a verified required interface.
use `case dyn ext:` only for the declared dynamic extension region.
```

### 6.5 Coverage witness

Every exhaustive match generates a hidden witness:

```text
StaticRequired(E) - StaticCovered(match) = {}
CompleteRequired(E, seal) - CompleteCoveredOrInterface(match) = {}
```

For critical:

```text
DynamicReachable(E, seal) = {}
```

These are compile/seal-time sets, not runtime tests.

---

## 7. Stable identity, tags, overflow, serialization, and frozen dispatch

### 7.1 Do not allocate dynamic IDs by load order

The earlier “static from zero upward, dyn from max downward” concept separates ranges but makes dynamic identities load-order dependent. Two machines loading modules in different orders could serialize different IDs for the same constructor.

Use two forms of identity:

```text
PersistentExtensionId:
    owner_enum_symbol_id
    provider_module_symbol_id
    constructor_local_id
    schema_abi_version

ProcessLocalTag:
    dense index assigned after static/complete configuration freeze
```

### 7.2 Persistent identity

Recommended canonical input:

```text
SimpleVariantIdentityV1 = hash(
    canonical enum SymbolId,
    canonical provider module SymbolId,
    canonical constructor name,
    provider-assigned stable local ordinal,
    payload schema ABI version
)
```

The full tuple remains in the manifest; the hash is an index/check, not the only collision authority.

### 7.3 Runtime tag layout

A practical runtime descriptor may use:

```text
tag class:
    00 static
    01 frozen complete
    10 open dyn
    11 invalid/reserved
```

However, after a configuration is sealed, static and complete variants should be reindexed into one dense local range:

```text
0 .. static_count - 1
static_count .. sealed_count - 1
DYN_MARKER + runtime_registry_index
```

This keeps static and complete dispatch near identical.

### 7.4 Serialization and cache rules

Never serialize the process-local dense tag.

Serialize:

```text
persistent variant identity
payload schema version
payload bytes/schema hash
complete-universe seal hash
```

Cache keys that can be affected by extension semantics include:

```text
compiler build identity
language edition
target/data layout
assurance profile
complete-universe seal
aspect weave-plan seal
relevant backend capability set
```

An aspect set that only supplies external tooling metadata and does not affect code or semantic analysis should not invalidate core code caches.

### 7.5 Overflow and collision checks

At manifest/seal time reject:

- static constructor count outside tag capacity;
- complete constructor count outside dense-tag capacity;
- provider-local ID reuse;
- persistent identity collision;
- payload size/alignment overflow;
- recursive payload without bounded/indirect representation;
- unsupported 32-bit layout;
- mismatched stable-ID tuple and claimed hash.

For tiny/RV32:

- keep core static tags compact;
- store dynamic descriptor indices separately when necessary;
- strip names/debug strings from runtime manifests;
- retain hashes/ABI/version/handler indices required for verification.

---

## 8. `Any` hardening policy

### 8.1 Final critical rule

> In the `critical` profile, the `Any` type is illegal in safe code. It is legal only lexically inside an unsafe block carrying the `type_erasure` capability and a reason. An `Any` value cannot leave that block unless converted to a non-`Any` safe type.

Recommended syntax aligned with Simple’s existing capability-scoped unsafe direction:

```simple
unsafe(
    reason: "decode legacy plugin payload",
    capabilities: [type_erasure]
):
    val raw: Any = legacy_plugin.read()
    val decoded: PluginMessage =
        checked_decode<PluginMessage>(raw)?
# raw is dead here; only decoded may leave
```

Equivalent annotation form can be supported if it matches existing parser conventions:

```simple
@unsafe(
    reason: "decode legacy plugin payload",
    capabilities: [type_erasure]
)
unsafe:
    ...
```

### 8.2 Profile matrix

| Use of `Any` | moderate | strict | robust | critical |
|---|---:|---:|---:|---:|
| Local scripting value | allow | warn when avoidable | warn/deny by package | deny outside unsafe |
| Public API | warn | deny | deny | deny |
| Field/global/container element | allow | warn | deny unless explicit dynamic package | deny outside unsafe; no escape |
| Cross-thread/task/process/device | warn | deny unclassified | deny | deny |
| Arithmetic/comparison/text conversion directly on `Any` | allow with runtime semantics | warn | deny unless checked dynamic API | deny |
| Checked downcast | allow | allow | allow in explicit dynamic API | only inside unsafe, result may leave |
| Unchecked downcast | unsafe | unsafe | unsafe | unsafe + capability + review/evidence |
| Compiler AST/HIR/MIR core storage | migration warning | deny new uses | deny | deny |

### 8.3 Why this restriction is justified in Simple now

The repository’s own Any-related bug record shows:

- raw untagged scalar storage into Any slots;
- bool/int/float tag confusion;
- interpreter/JIT divergence;
- comparison and text-conversion consumer gaps;
- duplicated boxing logic;
- a prior `Any + Any` native divergence;
- erased `Any` storage in monomorphization tables;
- closure/backend-port workarounds involving `any`-typed callable fields.

These are class-level representation hazards, not isolated syntax mistakes.

### 8.4 Safe replacement priority

When encountering `Any`, migrate in this order:

1. **Monomorphized generic**
   ```simple
   fn identity<T>(x: T) -> T:
       x
   ```

2. **Closed sum type**
   ```simple
   enum ScalarValue:
       Int(i64)
       Float(f64)
       Bool(bool)
       Text(text)
   ```

3. **Typed interface/trait object**
   ```simple
   interface Renderable:
       fn render(self) -> text
   ```

4. **Validated wire/FFI value**
   ```simple
   enum WireValue:
       Null
       Bool(bool)
       Integer(i64)
       Float(f64)
       Text(text)
       Bytes([u8])
       List([WireValue])
       Object(Dict<text, WireValue>)
   ```

5. **Opaque handle**
   ```simple
   newunit PluginHandle = u64
   ```

6. **Unsafe `Any` boundary**
   Used only when the source truly has no statically representable contract.

### 8.5 Critical Any escape analysis

Add `AnyEscapeChecker` after HIR type resolution.

Track:

```text
origin:
    literal cast
    FFI return
    dyn plugin return
    erased container read
    reflection

uses:
    type test
    checked downcast
    unchecked downcast
    store
    return
    capture
    suspend
    send/transfer
    operator
    call argument
```

Critical errors:

```text
Any created outside type_erasure unsafe capability
Any stored in object/global/container
Any returned or yielded
Any captured by closure/coroutine
Any live across await/yield
Any passed to non-unsafe function
Any sent to task/process/device
operator invoked on Any
Any leaves boundary without checked conversion
```

The checker must be type-resolved and dataflow-aware; a source-text lint is insufficient.

### 8.6 Representation-boundary wrapper

Provide a narrow standard API:

```simple
unsafe interface ErasedValueSource:
    fn read_any(self) -> Any

fn checked_downcast<T>(value: Any) -> Result<T, TypeMismatch>
fn checked_match(value: Any, schema: DynamicSchema) -> Result<ValidatedDynamic, DecodeError>
```

`checked_downcast` is callable only inside the `type_erasure` capability in critical, but its concrete `Result<T, ...>` can leave.

### 8.7 Compiler-internal Any migration

Priority targets include:

- monomorphization registries/tables;
- backend port callable fields;
- generic result dictionaries;
- AST/HIR payload extraction paths relying on rebinds from erased Dict values;
- temporary compiler APIs returning `Any`;
- runtime `BackendResult` aggregation where a closed result enum is possible.

No new compiler-core `Any` field should be accepted after the contract-lock wave.

---

## 9. Monomorphization design

### 9.1 Current source state

As of the inspected revision:

- `MonomorphizationTable` stores pending and specialized functions/structs/classes as `Any`;
- `process_pending()` records the original function without specializing it;
- `monomorphizer_specialize_function_internal()` returns the input unchanged;
- `process_specializations()` explicitly skips real specialization;
- `rewrite_module()` returns the module unchanged;
- `concrete_to_hir_type()` returns `HirTypeKind.Error`;
- `substitute_type()` and `substitute_expr()` are identity functions;
- the driver does not run a post-mono invariant check before reporting success.

Therefore the existing loud generic-native gates must remain in place until the replacement is proven end to end,
**with one narrowed exception landed 2026-08-22**: the *declaration-site* fatals for a generic CLASS and a generic
IMPL are replaced by step-12 non-emittable templating, because a template that is never instantiated is not a
defect and was blocking the stage1 closure on three uninstantiated sites. Loudness is not weakened -- it moves to
the use site (`E-MONO-030`/`E-MONO-032` in 40.mono, `HWIR-E-GENERIC` in strict MIR). The generic-STRUCT
declaration gate is untouched.

### 9.2 Typed data model

```simple
struct MonoSemanticKey:
    definition: StableSymbolId
    type_args: [CanonicalTypeId]
    const_args: [CanonicalConst]
    effect_args: [CanonicalEffect]
    capability_args: [CapabilityId]

struct MonoArtifactKey:
    semantic: MonoSemanticKey
    target: TargetTriple
    data_layout_hash: Hash
    cpu_feature_hash: Hash
    backend: BackendId
    assurance_semantics_hash: Hash
    complete_universe_hash: Hash
    weave_plan_hash: Hash
```

Only include profile/aspect fields when they change emitted semantics. Keep diagnostics-only policy outside the semantic key.

Typed tables:

```simple
class MonomorphizationTable:
    pending_functions: [(MonoSemanticKey, HirFunction)]
    pending_structs: [(MonoSemanticKey, HirStruct)]
    pending_classes: [(MonoSemanticKey, HirClass)]

    specialized_functions: Dict<MonoSemanticKey, HirFunction>
    specialized_structs: Dict<MonoSemanticKey, HirStruct>
    specialized_classes: Dict<MonoSemanticKey, HirClass>

    state: Dict<MonoSemanticKey, MonoState>
```

No `Any`.

### 9.3 Fixed-point algorithm

```text
1. Typecheck generic templates.
2. Resolve complete/aspect configuration and weave typed HIR.
3. Discover roots:
   - exported non-generic functions
   - entrypoints
   - statics
   - selected complete-extension handlers
   - aspect advice/facet entrypoints
   - required vtables/witnesses
4. Scan each root’s typed HIR for generic uses.
5. Canonicalize type/const/effect arguments.
6. Deduplicate by MonoSemanticKey.
7. Clone and recursively substitute the complete HIR body/signature/layout.
8. Insert specialized definition with stable mangled symbol.
9. Rewrite call/constructor/method references.
10. Scan each new specialization for more uses.
11. Repeat until the worklist is empty.
12. Remove or mark generic templates non-emittable.
13. Run post-mono verifier.
14. Lower only verified monomorphic HIR to canonical MIR.
```

### 9.4 Substitution coverage

The substitution visitor must explicitly cover:

- every `HirTypeKind`;
- function parameters and return;
- local annotations;
- expression result types;
- call type arguments;
- struct/class fields;
- enum payloads;
- trait bounds and associated projections;
- closures and captured types;
- optional/result/union members;
- pointer/reference/isolation qualifiers;
- effects/capabilities;
- layout/const generic expressions;
- aspect/facet witness types.

Generated exhaustive visitors should make a new HIR type/expr/stmt variant fail the compiler build.

### 9.5 Post-monomorphization invariants

Critical compilation fails unless:

```text
unresolved TypeParam count                 = 0
generic call/constructor/method count      = 0
generic emitted definition count          = 0
Any introduced as generic erasure count   = 0
HirTypeKind.Error created by substitution = 0
unknown type mangling count                = 0
unresolved associated projection count    = 0
target-width ambiguous layout count        = 0
missing drop/witness/vtable instance count = 0
```

### 9.6 Dynloaded generic code

A complete dynloaded module has two options:

1. **Pre-specialized manifest**
   ```text
   exports:
       map<i64,text>
       map<DeviceId,QueueId>
   ```
   All required instantiations are included and sealed.

2. **Template plus trusted compiler service**
   - only outside critical, or
   - critical compiler itself must generate, verify, sign, and extend a new seal before execution resumes.

Open runtime generation of unverified native code is not allowed in a fixed critical seal.

### 9.7 Code-size controls

Monomorphization trades dynamic dispatch for code size.

Use:

- canonical type IDs and deduplication;
- COMDAT/link-once equivalents;
- identical-code folding where backend-safe;
- specialization budgets per package;
- recursion-depth and growth-factor limits;
- warnings for unused generic parameters;
- later polymorphization of parameters proven representation/behavior irrelevant;
- size reports in the completeness manifest;
- explicit `@shared_generic` erased implementations only outside critical or behind an unsafe representation boundary.

Never silently fall back from a rejected mono budget to `Any`.

---

## 10. Sum types and evolving external data

### 10.1 Closed sum types are the default dynamic-value replacement

```simple
@closed
enum CompilerValue:
    Unit
    Bool(bool)
    Int(i64)
    Float(f64)
    Text(text)
    Symbol(SymbolId)
```

Critical rules:

- no wildcard in a match over `@closed`;
- every discriminant is validated on decode;
- every payload layout is canonical;
- all constructors and payloads participate in hash/serialize/visit/drop;
- unknown discriminants fail decode.

### 10.2 Evolving wire enums

For external protocols that must preserve unknown values:

```simple
@evolving(repr: u16, unknown: Unknown)
enum MessageKind:
    Start = 1
    Stop = 2
    Unknown(raw: u16)
```

Rules:

- `Unknown` is explicit and round-trippable;
- internal compiler IR remains closed;
- decoded unknown values cannot masquerade as a known variant;
- critical logic must explicitly decide whether `Unknown` is permitted.

### 10.3 Structural union syntax

Simple already has a union-type direction. In critical code:

```simple
type Scalar = i64 | f64 | bool | text
```

must lower to a canonical checked sum representation, not `Any`.

Required checks:

- normalized member order;
- duplicate/overlap detection;
- explicit tag;
- exhaustive narrowing;
- deterministic layout;
- no untagged reinterpretation;
- no ambiguous numeric coercion.

Prefer nominal enums for public ABI, persistence, and long-lived compiler IR.

### 10.4 Memory and performance

A conventional sum type costs:

```text
largest payload + discriminant + alignment
```

Optimizations such as niche encoding are allowed only after:

- a canonical layout contract exists;
- interpreter/JIT/native agree;
- invalid bit patterns remain impossible or checked;
- FFI/persistent layouts opt out unless explicitly versioned;
- translation validation covers the optimization.

---

## 11. Compiler missing-path prevention architecture

### 11.1 Four distinct completeness proofs

```text
1. Structural completeness
   every closed static enum variant is explicitly handled

2. Extension completeness
   every selected complete/dyn constructor implements required interfaces

3. Transition completeness
   every producer output has a declared next-stage action

4. Semantic-subcase completeness
   significant cases inside broad variants are enumerated and tested
```

A fifth cross-cutting proof is bootstrap/engine parity.

### 11.2 Canonical compiler schema registry

Generate one registry from authoritative declarations:

```text
GrammarProduction
TokenKind
FlatDeclKind / FlatStmtKind / FlatExprKind
AstItemKind / StmtKind / ExprKind / TypeKind / PatternKind
HirItemKind / HirStmtKind / HirExprKind / HirTypeKind
MirStmt / MirTerminator / MirInst / MirTypeKind
InterpreterOp
BackendOp / ISA family
```

Each row has stable identity and schema metadata.

Example:

```sdn
variant:
  id: spl:variant@compiler.frontend.ExprKind.Spawn~...
  owner: compiler.frontend.ExprKind
  domain: static
  payload_schema: Spawn(Expr)
  since_edition: 2026
```

### 11.3 Total transition declarations

Each boundary declares a total relation.

```sdn
transition:
  from: FlatExprKind.Spawn
  to: ExprKind.Call
  state: normalized
  reason: "spawn consumers use builtin Call identity"
  test: flat_bridge_spawn_call_expr_spec
```

Allowed states:

```simple
enum CoverageState:
    Implemented
    Normalized(target: StableVariantId)
    Unsupported(reason: text, issue: text?)
    NotApplicable(reason: text)
```

`Missing` is not a valid checked-in state. It is the result of set subtraction and fails the build.

### 11.4 Negative-space checker

For every boundary:

```text
Missing =
    ProducerUniverse
  - Implemented
  - Normalized
  - Unsupported
  - NotApplicable
```

Build invariant:

```text
Missing = {}
```

For extension handlers:

```text
MissingCapabilities =
    RequiredCapabilities(constructor)
  - ProvidedCapabilities(constructor)
```

Seal invariant:

```text
MissingCapabilities = {}
```

### 11.5 Generated visitors

Generate:

- read-only recursive visitor;
- mutable rewrite visitor;
- child enumeration;
- hash/serialize visitor;
- source-span visitor;
- critical safety visitor skeleton;
- pretty-printer skeleton;
- coverage table.

A new variant causes generated interfaces and exhaustive matches to fail until regenerated and handled.

### 11.6 No silent fallback

Forbidden in compiler transformations:

```simple
case _:
    NilLit

case _:
    Error

case _:
    pass

case _:
    0

case _:
    scalar_fallback(...)
```

Allowed only when the wildcard is over an explicitly open `dyn` region and the action is a typed dynamic dispatch or an explicit diagnostic.

### 11.7 Semantic subcase registries

Structural coverage does not prove all cases inside `Call`, `Named`, or `Binary`.

Maintain declarative subcase sets such as:

```text
Call:
  ordinary
  builtin
  primitive_cast
  constructor
  module_qualified
  method/UFCS
  spawn_normalization
  host_lane
  gpu_lane
  dyn_interface
  complete_handler
```

Each subcase has at least:

- parser/source fixture;
- HIR snapshot;
- MIR snapshot;
- interpreter oracle;
- JIT/native result;
- negative diagnostic fixture where relevant.

### 11.8 Coverage command

Add:

```text
simple compiler coverage
simple compiler coverage --profile=critical
simple compiler coverage --stage ast-to-hir
simple compiler coverage --format=sdn
```

Example output:

```text
Compiler completeness seal candidate

Static variants
  grammar -> FlatAst       153/153
  FlatAst -> AST           153/153
  AST -> HIR               141/141
  HIR type -> MIR type      26/26
  HIR expr -> MIR expr      74/74
  MIR -> interpreter        98/98
  MIR -> LLVM               98/98
  MIR -> Cranelift          98/98

Explicit unsupported
  AST ExprKind.Atom          1 reason+issue present
  AST ExprKind.New           1 reason+issue present

Missing                              0
Silent fallback sites                0
Critical wildcard sites              0
```

### 11.9 Coverage report must be generated, never hand-maintained

Reports may summarize the generated manifest but cannot be the source of truth. A stale “complete” document cannot satisfy a release gate.

---

## 12. Critical compiler pipeline and ordering

### 12.1 Recommended ordering

```text
1. Resolve profile/config.
2. Parse all selected source/module manifests.
3. Validate grammar and FlatAst/AST transition coverage.
4. Lower to typed HIR.
5. Resolve names/types/effects/ownership.
6. Run safety/unsafe/Any checks.
7. Resolve selected complete extensions and aspects.
8. Verify manifests, ABIs, handlers, effects, dependencies, signatures.
9. Weave/normalize typed HIR.
10. Repeat type/effect/ownership/safety checks on woven HIR.
11. Run monomorphization fixed point.
12. Run post-mono verifier.
13. Enforce normalization barrier: no open dyn nodes in critical canonical HIR.
14. Lower to canonical MIR.
15. Run MIR structural/transition/safety verifier.
16. Optimize with verified preservation contracts.
17. Interpret canonical MIR as reference.
18. Lower to JIT/native backends.
19. Differentially validate selected critical fixtures.
20. Emit artifact and evidence seal.
```

### 12.2 Why aspects must be resolved before final monomorphization

Typed advice/facet weaving can introduce:

- calls to generic advice helpers;
- new witness/vtable requirements;
- different effects/capabilities;
- new control-flow edges;
- additional unsafe boundaries.

Therefore the final monomorphization and safety closure must see the post-weave HIR.

### 12.3 Normalization barriers

Recommended openness:

```text
source AST:
    static + complete + dyn allowed by profile

typed pre-weave HIR:
    static + complete
    dyn only outside critical

canonical post-mono HIR:
    static core
    explicitly permitted frozen complete dialect ops only

canonical MIR:
    closed static core
    or a finite sealed complete backend dialect set

machine/backend IR:
    backend-specific sealed dialect
```

Prefer normalizing extensions into canonical core operations before MIR. Retain a complete dialect op only when normalization would destroy required semantics or optimization structure.

---

## 13. Verified dynload and aspect architecture

### 13.1 Complete dynload

A dynloaded module becomes semantically complete through:

```text
manifest discovery
  -> dependency resolution
  -> stable identity check
  -> ABI/schema check
  -> required-interface check
  -> effect/capability check
  -> transition/normalization check
  -> signature/trust check
  -> proof/evidence check as required
  -> dense local tag assignment
  -> dispatch-table generation
  -> completeness seal
  -> code load/relocation
  -> atomic publication
```

The module file remains separate; the semantic world is closed.

### 13.2 Required constructor/operation contract

Example:

```sdn
extension:
  owner_enum: compiler.hir.HirExprKind
  constructor: gpu.MatrixMultiply
  closure: complete
  payload_schema_hash: "..."
  module_abi_hash: "..."
  required_core_abi_hash: "..."

  provides:
    verify: gpu.verify_matrix_multiply
    type_check: gpu.type_matrix_multiply
    effects: gpu.effects_matrix_multiply
    visit_children: gpu.visit_matrix_multiply
    lower_mir: gpu.lower_matrix_multiply
    print: gpu.print_matrix_multiply
    hash: gpu.hash_matrix_multiply
    serialize: gpu.serialize_matrix_multiply
```

If the constructor is normalized before HIR/MIR:

```sdn
  transition:
    ast_to_hir:
      state: normalized
      target: compiler.hir.HirExprKind.Call
```

Downstream operations become `NotApplicable(reason)` only after the normalizer is verified total.

### 13.3 Aspect facets

Retain the proposed model:

- facet interfaces are statically typed;
- dynamic facets use external witnesses/sidecars;
- base object layout and nominal hierarchy do not change;
- optional access is explicit;
- required bindings are complete and unique;
- aspect identity is independent of file placement;
- catalog routing avoids directory scans;
- modules/chunks remain independently loadable.

### 13.4 Aspect completeness seal

A critical aspect seal contains:

```text
selected aspects and versions
pointcut expansion result
matched joinpoint IDs
advice ordering and conflict resolution
facet bindings by concrete type
required witness handlers
effects and unsafe capabilities
base/public/layout ABI hashes
module/content/index/signature hashes
weave plan hash
post-weave HIR hash
proof/evidence references
activation policy
```

### 13.5 Aspect lifecycle

```simple
enum AspectState:
    Catalogued
    Resolved
    Verified
    Loaded
    Staged
    Bound
    Sealed
    Active
    Failed(AspectError)
```

Critical rules:

- no transition from `Active` back to unloaded for semantics-bearing aspects;
- no publication before every required module/binding is staged;
- one generation/epoch is published atomically;
- failed activation publishes nothing;
- no late aspect added after seal;
- first-use loading may map/decompress already verified content but cannot change the seal.

### 13.6 Advice modes and overhead

| Mode | Core code change | Disabled hot-path cost | Critical |
|---|---|---:|---:|
| omitted | none | zero | yes |
| explicit facet acquisition | none in ordinary business path | zero until explicit call | yes |
| static weave | direct code | normal woven cost | yes |
| sealed complete patchpoint | predeclared patchpoint | architecture-specific NOP/guard | only if included in seal and measured |
| open dyn patchpoint | runtime registry/patch | nonzero metadata/guard | no |
| hot reweave | code mutation | variable | no |

### 13.7 Current aspect-pack implementation integration

Build on the existing catalog/container slice rather than replacing it. Complete the missing semantic pieces in this order:

1. typed facet grammar and HIR;
2. type-level binding completeness/uniqueness;
3. witness/sidecar ABI;
4. core public ABI comparison;
5. signature/trust verification;
6. atomic generation publication;
7. compiler weave-plan production;
8. post-weave critical verification;
9. multi-profile catalog only after an actual consumer exists;
10. hot unload remains out of critical scope.

---

## 14. Critical profile rules added by this plan

Reserve new requirement identifiers in the existing critical requirements document.

### 14.1 `REQ-MC-ANY-001` — unsafe-only `Any`

- `Any` outside `unsafe(capabilities:[type_erasure])` is a hard error.
- `Any` cannot escape the unsafe region.
- direct operators on `Any` are prohibited.
- checked conversion must produce a concrete type, sum type, typed interface, or validated opaque wrapper.

### 14.2 `REQ-MC-MONO-001` — monomorphic canonical IR

- no unresolved generic/type parameter reaches canonical MIR;
- no generic erasure to `Any`;
- all reachable instantiations are in the mono graph and seal;
- unsupported generic forms fail before codegen.

### 14.3 `REQ-MC-COMPLETE-001` — static and complete closure

- all static variants are exhaustively handled;
- all selected complete variants implement required interfaces;
- no open dyn constructor is reachable;
- no wildcard closes a compiler-IR match.

### 14.4 `REQ-MC-PIPE-001` — total stage transitions

- every producer variant has an explicit transition state;
- missing mapping is a build error;
- silent fallback replacements are prohibited.

### 14.5 `REQ-MC-ASPECT-001` — sealed aspect world

- all semantics-changing aspects are selected before weave;
- post-weave program is rechecked;
- weave plan is part of artifact identity;
- no late semantic aspect activation.

### 14.6 `REQ-MC-BOOT-001` — bootstrap and engine parity

- seed and self-hosted compiler use the same generated feature/coverage manifest;
- accepted/rejected critical fixture sets match;
- interpreter/JIT/native semantic differentials are zero for the critical conformance corpus.

---

## 15. Migration plan for Simple itself

Do not flip the whole repository to critical in one change. Migrate by executable gates while preserving fail-closed boundaries.

### Phase 0 — Contract lock and truth inventory

Deliver:

- canonical schema registry format;
- completeness state enum;
- static/complete/dyn semantics;
- stable extension identity;
- Any unsafe capability;
- typed mono keys;
- aspect seal schema;
- generated diagnostic ID ranges;
- package migration inventory.

Run source census for:

```text
Any declarations/fields/returns/params
wildcard matches in compiler
NilLit/Error/pass/default fallbacks
unhandled enum variants
generic definitions/calls
unsafe operations
aspect/dyn registration points
duplicate semantic tables
engine-specific behavior fixtures
```

No behavior change yet, but the inventory becomes machine-readable.

### Phase 1 — Make missing paths loud everywhere

- replace silent FlatAst/AST/HIR/MIR fallbacks with explicit diagnostics;
- add total transition tables;
- generate exhaustive visitors;
- make critical wildcard rules fatal;
- give all 26 current `HirTypeKind` variants explicit MIR decisions;
- convert unsupported cases to named errors with source spans;
- add `simple compiler coverage`.

Exit gate:

```text
missing static transition = 0
silent semantic fallback = 0
critical compiler wildcard = 0
```

### Phase 2 — Any boundary and representation stabilization

- implement `type_erasure` unsafe capability;
- add HIR Any escape analysis;
- fix remaining Any storage/consumer parity bugs before using unsafe Any as a supported boundary;
- define one canonical RuntimeValue boxing/unboxing API;
- replace duplicated boxing logic with generated type-directed conversion;
- migrate compiler registries from `Any` to typed records;
- migrate broad dynamic data to explicit `WireValue`/result enums;
- ban new compiler-core Any uses.

Migration severity:

```text
moderate: inventory/advisory
strict:   warning, public API deny
robust:   deny compiler core and boundaries
critical: deny outside unsafe; deny escape
```

### Phase 3 — Typed monomorphization

- replace all mono `Any` tables;
- implement full recursive substitution;
- implement call/constructor/method collection;
- clone specialized definitions;
- rewrite call sites;
- deterministic fixed-point collection;
- post-mono verifier;
- preserve current early generic gates until all positive/negative fixtures pass;
- only then relax supported tiers one at a time.

Order of generic support:

```text
1. free function, one inferred concrete type arg
2. multiple type args and explicit type args
3. generic structs
4. generic classes
5. generic methods
6. generic enums, without breaking Option/Result
7. trait bounds and associated projections
8. const generics/layout parameters
9. closures/drop glue/witness generation
```

### Phase 4 — Sum types and closed match enforcement

- finish `@closed` and `@evolving`;
- preserve enum payload metadata end to end;
- canonical union lowering;
- invalid discriminant checks;
- critical no-wildcard enforcement;
- replace compiler Any result/value families with closed enums;
- generated match-coverage witnesses.

### Phase 5 — Complete/dyn extension infrastructure

- implement `complete:` / `dyn:` enum extension grammar;
- generate extension manifests;
- verify required interfaces;
- freeze dense local IDs;
- seal config-specific universes;
- cache by seal hash;
- preserve stable persistent IDs in serialized HIR/SMF;
- prohibit open dyn in critical.

### Phase 6 — Aspect compiler integration

- typed facet grammar/HIR;
- explicit witness/sidecar interfaces;
- pointcut expansion over stable semantic IDs;
- weave typed HIR before final mono;
- re-run safety/type/effect checks;
- atomic aspect generation publication;
- post-weave seal/evidence;
- integrate existing aspect-pack loader.

### Phase 7 — Seed/self-host parity and bootstrap closure

- generate the same schema/coverage tables for Rust seed and Simple compiler;
- add parity command:
  ```text
  simple compiler parity --seed bin/simple-seed --self bin/simple
  ```
- compare:
  - parser productions;
  - enum variants/discriminants;
  - transition states;
  - diagnostics;
  - accepted/rejected fixtures;
  - HIR/MIR snapshots;
  - unsafe and Any policy;
  - complete/aspect manifest interpretation.
- make Stage N build Stage N+1 with the same critical feature seal;
- require two consecutive self-host stages to produce equivalent manifests and reproducible artifacts.

### Phase 8 — Critical islands to whole-compiler migration

Suggested package order:

```text
00.common schemas/policy
10.frontend canonical parser and bridge
20.hir types/visitors/coverage
30.types and 35.semantics
40.mono
50.mir
55.borrow / verification prerequisites
70.backend core lowering
80.driver
90.tools coverage/seal commands
95.interp reference engine
99.loader
runtime and selected stdlib
SimpleOS/firmware critical packages
```

Each package gets a `simple.sdn` critical pin only after:

- no local waiver without expiry/owner;
- its dependency closure is at least robust;
- all critical checks actually execute;
- differential tests cover its semantics.

### Phase 9 — Release evidence and default escalation

Critical release requires:

```text
static coverage             100%
selected complete coverage  100%
missing transition count       0
Any outside unsafe              0
Any escape                      0
unresolved generic in MIR       0
silent fallback                 0
reachable unsupported           0
seed/self-host parity diff      0
interpreter/JIT/native diff     0
unverified aspect               0
late dyn semantic module        0
stale evidence                  0
```

Only then consider escalating compiler/loader defaults from robust-at-warning to robust-deny or critical for selected release lanes.

---

## 16. Configuration examples

### 16.1 Normal development compiler

```sdn
compiler:
  assurance: moderate

  extensions:
    complete:
      - hir_async
      - hir_gpu

    dyn:
      - ide_plugins
      - experimental_analysis

  linkage:
    hir_async: dynload
    hir_gpu: dynload

  activation:
    hir_async: startup
    hir_gpu: first_use
    ide_plugins: manual
```

### 16.2 Robust compiler

```sdn
compiler:
  assurance: robust

  extensions:
    complete:
      - hir_async
      - hir_gpu
      - hir_verify

    dyn:
      - ide_plugins

  policy:
    any_public_api: deny
    compiler_core_any: deny
    missing_transition: deny
    silent_fallback: deny
```

### 16.3 Critical sealed compiler

```sdn
compiler:
  assurance: critical

  extensions:
    complete:
      - hir_async@3
      - hir_verify@2
      - backend_llvm@5

    dyn: []

  aspects:
    complete:
      - security.audit@4
      - trace.critical@2

  seal:
    require_signatures: true
    require_post_weave_verification: true
    prohibit_late_semantic_activation: true
    prohibit_hot_unload: true
    require_seed_selfhost_parity: true
```

### 16.4 Dynloaded but complete module

```sdn
module:
  id: hir_async
  linkage: dynload
  closure: complete
  activation: first_use

  extends:
    - enum: compiler.hir.HirExprKind
      constructor: async.Await
      schema_abi: 2

  provides:
    - HirVerify
    - HirEffects
    - HirVisit
    - HirLowerMir
    - HirPrint
    - HirSerialize
```

The module is verified and included in the seal before execution. First use may load bytes, but cannot alter the selected semantic universe.

---

## 17. Diagnostic examples

### 17.1 Any outside unsafe

```text
E-MC-ANY-001:
`Any` is unavailable in safe critical code

  val result: Any = backend.run()
              ^^^

replace with:
  - a monomorphized generic,
  - a closed sum type,
  - a typed interface,
  - or an unsafe type_erasure boundary with checked conversion
```

### 17.2 Any escape

```text
E-MC-ANY-002:
erased value escapes its type_erasure boundary

  return raw
         ^^^

`raw: Any` originated at plugin.read().
convert it to a concrete or closed-sum type before leaving the unsafe block.
```

### 17.3 Static variant hidden by wildcard

```text
E-COMPLETE-001:
non-exhaustive static match over HirExprKind

missing:
  HirExprKind.HostGpuLane

`case complete` and `case dyn` do not cover static variants.
wildcards are forbidden for critical compiler IR.
```

### 17.4 Missing complete handler

```text
E-COMPLETE-021:
complete extension gpu.MatrixMultiply cannot be sealed

required interface missing:
  HirSerialize

provider:
  hir_gpu@7
payload schema:
  2d15...
```

### 17.5 Unresolved generic after mono

```text
E-MONO-031:
type parameter `T` reached the post-monomorphization verifier

definition:
  storage.map.insert<T>

instantiation chain:
  main -> build_index -> insert<Record>

no MIR or object file was emitted.
```

### 17.6 Open dyn in critical

```text
E-MC-DYN-001:
open dynamic semantic extension is reachable in a critical build

enum:
  HirExprKind

provider:
  ide.LiveProbe

select and seal the provider as `complete`, normalize it before the critical
barrier, or exclude it from this configuration.
```

---

## 18. Performance and memory design

### 18.1 Static and complete paths

```text
static:
    direct dense tag switch

complete after seal:
    same dense local tag space or compact function table
```

Expected design overhead for static nodes:

- no extra per-node field;
- no hash lookup;
- no descriptor dereference;
- only the normal discriminant switch.

Expected design overhead for complete nodes after seal:

- one dense tag;
- direct switch or indexed handler table;
- global descriptors only;
- no runtime string lookup.

### 18.2 Open dyn path

Open dyn incurs:

- dynamic-region check;
- registry/descriptor lookup or cached index;
- indirect interface call;
- module metadata and lifecycle state.

This is appropriate for genuinely late extensions, not for core compiler IR hot paths.

### 18.3 Any removal

Removing Any from critical hot code improves:

- constant propagation;
- direct operator selection;
- alias/type reasoning;
- stack/register allocation;
- elimination of boxing/tag checks;
- engine parity;
- proof tractability.

### 18.4 Monomorphization tradeoff

Benefits:

- concrete layout and calling convention;
- direct dispatch and inlining;
- no erased value/tag overhead;
- stronger post-pass invariants.

Costs:

- code-size growth;
- compile-time work;
- cache-key cardinality.

Mitigations are the deduplication and budget mechanisms in Section 9.7. A budget failure is explicit; it never changes semantics to erased Any.

### 18.5 Sparse extension metadata

Use side tables:

```text
NodeId -> TypeInfo
NodeId -> OwnershipInfo
NodeId -> GpuInfo
NodeId -> ProofInfo
```

rather than adding optional dynamic dictionaries to every node. Core fields remain inline; sparse annotations pay only when present.

### 18.6 Aspect overhead

State exact contracts:

- omitted: zero code/data path impact except optional catalog entry if packaged;
- explicit facet: zero ordinary path impact;
- static weave: ordinary direct cost;
- sealed patchpoint: architecture-measured NOP/branch footprint;
- open dyn advice: not permitted to claim zero overhead.

---

## 19. Verification and test strategy

### 19.1 Generated structural tests

For every declared variant:

- construct minimal value/source;
- traverse;
- hash;
- serialize/deserialize;
- pretty-print;
- transition to next stage;
- prove unsupported diagnostic when intentional.

### 19.2 Defect-class tests

Pin the known classes:

- unknown FlatAst expression cannot become `NilLit`;
- unknown statement cannot become empty block;
- unknown HIR type cannot hit an undifferentiated wildcard;
- Any scalar store/compare/text conversion across all engines;
- generic template cannot reach MIR;
- bool payload boxing uses boolean representation;
- omitted handler blocks complete-module seal;
- late aspect cannot match already sealed code;
- corrupted persistent/dense variant mapping is rejected.

### 19.3 Engine differential matrix

For every critical semantic fixture:

```text
parser/AST snapshot
HIR snapshot
post-weave HIR snapshot
post-mono HIR snapshot
MIR snapshot
interpreter result
JIT result
LLVM native result
Cranelift native result
```

Compare semantic result and diagnostics, not machine-specific addresses.

### 19.4 Bootstrap matrix

```text
Rust seed -> Simple stage 1
Simple stage 1 -> stage 2
stage 2 -> stage 3
stage 3 -> stage 4/redeploy
```

At each edge compare:

- registry/schema hash;
- feature/completeness seal;
- accepted/rejected corpus;
- diagnostics IDs;
- mono graph summary;
- aspect configuration;
- emitted ABI manifests.

### 19.5 Mutation testing

Deliberately inject:

- a new enum variant without a consumer;
- a missing bridge map;
- a complete extension missing one handler;
- a bogus Any tag;
- an identity substitution in mono;
- a late aspect;
- an invalid enum discriminant;
- a stale evidence hash.

The release gate must turn red for every injection.

### 19.6 Fuzz and property tests

Properties:

```text
deserialize(serialize(x)) = x
persistent_id -> dense_tag -> persistent_id is bijective within seal
static/complete/dyn domains never overlap
mono substitution removes every bound TypeParam
post-mono verifier rejects an injected TypeParam
all engines agree on closed sum operations
Any checked conversion never fabricates a value
failed aspect activation publishes no binding
```

### 19.7 Formal verification targets

Prioritize small, load-bearing kernels:

- set-difference completeness equation;
- persistent-to-dense ID bijection;
- mono substitution preservation;
- no-TypeParam postcondition;
- sum discriminant validity;
- aspect activation atomicity;
- Any non-escape dataflow;
- parent-authoritative parallel result commit.

Proofs complement executable checks; they do not replace missing runtime/backend tests.

---

## 20. Parallel-agent implementation plan

> Execution status for this plan (living, per-commit rows, Phase 1 stage1 state): see §27.

### 20.1 Coordination rule

Use the repository’s existing principle:

> Shared contracts first, then parallel work with disjoint file ownership. A single integration owner edits shared dispatchers, root exports, profile tables, and aggregate release gates.

Every agent receives:

```sdn
agent_scope:
  id: ...
  allow: [...]
  deny: [...]
  inputs: [...]
  outputs: [...]
  red_tests: [...]
  exit_gate: ...
```

CI rejects out-of-scope edits.

### 20.2 Wave 0 — serial contract lock

**Owners:** Architect A0 + independent reviewer R0.

Freeze:

- semantic closure schema (`static|complete|dyn`);
- linkage/activation axes;
- stable extension identity;
- `CoverageState`;
- required compiler operation interfaces;
- Any unsafe capability and escape rules;
- mono semantic/artifact key;
- aspect seal and lifecycle;
- diagnostics;
- generated registry format;
- test/evidence receipt format.

Shared outputs:

```text
doc/02_requirements/language/critical_completeness.md
doc/04_architecture/compiler/extension_completeness.md
src/compiler/00.common/completeness/**
src/compiler/00.common/dynamic_identity/**
spec/compiler_schema/**
```

No feature agent starts until both reviewers sign the contract hash.

### 20.3 Wave 1 — independent foundations

| Agent | Exclusive ownership | Deliverable | Exit gate |
|---|---|---|---|
| A1 Schema generator | `tools/compiler_schema/**`, `spec/compiler_schema/**` | Extract enum/IR variants and generate registries/visitors | deterministic regeneration, clean diff |
| A2 Exhaustiveness | new `20.hir/exhaustiveness/**`, match-coverage tests | static/complete/dyn coverage witnesses; critical wildcard ban | injected variant fails |
| A3 Transition model | new `compiler/00.common/transition/**` | `CoverageState`, set-difference validator, SDN format | missing row fails |
| A4 Dynamic identity | `00.common/dynamic_identity/**` | persistent IDs, collision/overflow checks, dense freeze map | bijection/property specs |
| A5 Unsafe capability | `00.common/assurance/**`, new capability schema only | `type_erasure` capability contract | parser/model roundtrip |
| A6 Test harness | `test/01_unit/compiler/completeness/**`, scripts under new path | generated defect-class harness | deliberate false-green caught |
| A7 Perf baseline | `test/04_benchmark/compiler_hardening/**` | baseline static enum, Any, mono, dispatch, aspect metrics | reproducible measurement report |

Shared driver/parser files remain denied in Wave 1.

### 20.4 Wave 2A — compiler path completeness

| Agent | Ownership | Work |
|---|---|---|
| C1 Grammar registry | `10.frontend/core` schema adapters, not shared parser dispatcher | grammar/token registry extraction |
| C2 FlatAst bridge | `_FlatAstBridge/**` | replace dispatch chains/defaults with generated total mapping |
| C3 AST visitors | parser type visitor modules | generated child/serialize/hash visitors |
| C4 HIR visitors | new `20.hir/generated/**` | exhaustive expr/stmt/type/item visitors |
| C5 HIR→MIR types | `_MirLowering/function_lowering` via isolated shard or patch submitted to integrator | explicit decisions for all `HirTypeKind` |
| C6 HIR→MIR expr/stmt | new transition fragments | complete mapping registry |
| C7 Backend coverage | backend-specific generated shards | no scalar/zero fallback |
| C8 Interpreter coverage | `95.interp` generated shards | MIR op coverage parity |

Agents do not edit a common enum or driver; generated fragments are merged by I0.

### 20.5 Wave 2B — Any hardening

| Agent | Ownership | Work |
|---|---|---|
| Y1 Any inventory | `tools/any_audit/**` | typed census and escape graph |
| Y2 HIR checker | new `35.semantics/any_escape/**` | unsafe-only and non-escape enforcement |
| Y3 RuntimeValue ABI | one new canonical runtime value module + tests | central box/unbox/compare/render contract |
| Y4 Rust-seed parity | Rust compiler Any checking/lowering modules | same diagnostics and semantics |
| Y5 Self-hosted boxing parity | pure-Simple MIR Any conversion module | remove duplicated per-consumer conversions |
| Y6 Migration wrappers | new typed value/sum modules | `WireValue`, `CompilerValue`, typed backend results |
| Y7 Boundary tests | isolated Any differential specs | interpreter/JIT/native matrix |

Y3 locks the ABI before Y4/Y5 modify lowering.

### 20.6 Wave 2C — typed monomorphization

| Agent | Ownership | Work |
|---|---|---|
| M1 Mono types/table | `40.mono/monomorphize/types*`, new table module | remove all Any storage |
| M2 Type substitution | `40.mono/monomorphize/type_subst.spl` | exhaustive recursive type substitution |
| M3 HIR substitution | new `40.mono/monomorphize/hir_subst/**` | expr/stmt/block/function substitution |
| M4 Collector | new `40.mono/monomorphize/collector/**` | root/use worklist and fixed point |
| M5 Rewriter | `40.mono/monomorphize/rewriter/**` | symbols, defs, call/constructor/method rewrites |
| M6 Layout/type instances | specialized struct/class/enum shards | concrete layout generation |
| M7 Post-mono verifier | new `40.mono/verify/**` | zero unresolved generic invariants |
| M8 Rust-seed parity | corresponding Rust mono/gate tests | feature and diagnostic parity |
| M9 Code-size/cache | mono artifact/cache modules | deterministic keying, dedup, reports |

The integrator alone changes `driver_hir_pipeline_passes.spl` and relaxes gates after M1–M7 pass.

### 20.7 Wave 2D — sum types and enum contracts

| Agent | Ownership | Work |
|---|---|---|
| S1 Enum payload preservation | parser enum payload modules | payload metadata end to end |
| S2 `@closed` | new enum-contract checker | no wildcard, invalid discriminant rejection |
| S3 `@evolving` | wire enum module | explicit unknown preservation |
| S4 Union normalization | type-system union modules | canonical members and checked narrowing |
| S5 Layout/serialization | enum/union layout shard | stable ABI and roundtrip |
| S6 Any-to-sum migration | selected compiler result modules | replace erased value families |

### 20.8 Wave 2E — complete/dyn and aspects

| Agent | Ownership | Work |
|---|---|---|
| D1 Extension grammar | parser extension hooks only | `complete:` / `dyn:` declarations |
| D2 Manifest generator | new compiler extension manifest modules | required interfaces and transitions |
| D3 Sealer | new `99.loader/completeness_seal/**` | verify/freeze/dense IDs |
| D4 Loader admission | aspect/module loader shard | ABI/signature/dependency verification |
| D5 Atomic registry | new runtime generation registry | staged publish and failure rollback |
| D6 Facet grammar/HIR | new facet parser/HIR modules | typed facet declarations/bindings |
| D7 Witness/sidecar | new runtime facet modules | stable base layout and explicit acquisition |
| D8 Pointcut/weave plan | AOP planner modules | stable joinpoint expansion and conflicts |
| D9 Typed weaver | AOP HIR weave modules | post-weave typed HIR |
| D10 Aspect pack integration | existing aspect-pack adapter only | connect semantic manifest to current routed loader |
| D11 Critical aspect policy | assurance aspect checker | no late/open semantic aspect |
| D12 Aspect evidence | tests/reports | weave seal, atomicity, performance |

D4 must not claim signature enforcement until a real verifier and authority are wired.

### 20.9 Wave 3 — migration agents

Partition by package; no two agents edit one package.

Suggested shards:

```text
P1 compiler 00.common + policy
P2 frontend parser/bridge
P3 HIR
P4 type/semantics
P5 MIR/borrow
P6 backend LLVM
P7 backend Cranelift
P8 interpreter
P9 driver/tools/loader
P10 runtime/common library
P11 OS/firmware unsafe boundaries
P12 apps/tooling dynamic values
```

Each shard:

1. runs Any/fallback/generic census;
2. converts safe cases;
3. adds critical package pin;
4. supplies engine and negative tests;
5. submits no shared-root edits.

### 20.10 Wave 4 — parallel validation

Independent agents:

| Agent | Attack |
|---|---|
| V1 Structural mutation | add variants/remove mapping rows |
| V2 Any red-team | escape via aliases, containers, closures, async, FFI |
| V3 Mono red-team | recursive/multi-module/associated/target-width cases |
| V4 Dynamic red-team | ID collisions, load order, missing handlers, stale ABI |
| V5 Aspect red-team | partial binding, order conflict, failed activation, late match |
| V6 Engine differential | interpreter/JIT/LLVM/Cranelift |
| V7 Bootstrap | seed/self-host/stage parity |
| V8 Fuzz/property | serialization, tags, manifests |
| V9 Perf/memory | static/complete/dyn and code-size regression |
| V10 Evidence | stale/missing/fabricated receipt injection |
| V11 Formal | proof obligation and assumption audit |
| V12 Parallel ownership | cross-task/process/device Any/pointer escape |

### 20.11 Wave 5 — serial integration and release gate

**Single integration owner I0** edits:

- root exports;
- shared parser dispatch;
- central driver ordering;
- profile severity table;
- generated registry inclusion;
- release aggregate;
- default profile escalation.

**Independent release reviewer R1** verifies:

- all generated files reproducible;
- no out-of-scope agent edits;
- no bypass environment flag accepted in critical;
- no checker ran advisory when critical;
- every evidence receipt fresh and bound to artifact/seal hash.

---

## 21. Parallel-agent dependency graph

```text
Wave 0 contract lock
  |
  +--> A1 schema ----+--> C2/C3/C4/C5/C6/C7/C8
  |
  +--> A2 coverage --+-----------------------+
  |
  +--> A4 identity ----> D2/D3/D4/D5 ------+--> D6..D12
  |
  +--> A5 unsafe ------> Y1/Y2 ------------+--> migration
  |                         |
  |                         +--> Y3 --> Y4/Y5/Y6/Y7
  |
  +--> mono contract -----> M1 --> M2/M3 --> M4/M5/M6 --> M7/M9
  |
  +--> enum contract -----> S1 --> S2/S3/S4/S5 --> S6

all Wave 2 lanes
  -> package migration
  -> red-team/engine/bootstrap/perf
  -> serial integration
  -> critical release seal
```

No agent may relax a fail-closed gate before the corresponding positive and negative end-to-end lane is green.

---

## 22. Acceptance criteria

### 22.1 Language/compiler

- `case dyn` cannot cover static or complete members.
- `case complete` requires a verified operation interface.
- `_` cannot close an exhaustive critical compiler match.
- selected complete modules are deterministic and sealed.
- open dyn semantic constructors are unreachable in critical.
- all stage transitions are explicit.
- all current `HirTypeKind` variants have explicit MIR decisions.
- no silent default replacement remains.

### 22.2 Any

- critical safe code cannot mention `Any`;
- Any unsafe boundaries require reason and `type_erasure`;
- Any cannot escape;
- all engines agree on the checked dynamic-value corpus;
- compiler-core erased registries are gone;
- direct Any arithmetic/comparison/rendering is absent in critical.

### 22.3 Generics

- typed mono tables only;
- deterministic fixed point;
- all supported generic forms specialize correctly;
- unsupported forms fail before MIR/codegen;
- post-mono unresolved count is zero;
- target width/layout is part of artifact identity;
- no fallback to Any.

### 22.4 Dynload/aspects

- manifest required handlers complete;
- stable IDs independent of load order;
- dense tags bijective within a seal;
- ABI/signature/dependency checks execute;
- failed activation publishes nothing;
- critical weave plan fixed before final verification;
- no hot semantic reload/unload;
- omitted aspect has measured zero path cost;
- patchpoint modes report exact measured cost.

### 22.5 Bootstrap/release

- Rust seed and Simple self-host manifests match;
- critical accepted/rejected fixture sets match;
- two consecutive self-host stages produce equivalent seals;
- interpreter/JIT/native differential failures are zero;
- evidence is fresh, reproducible, and artifact-bound.

---

## 23. Rejected alternatives

### 23.1 Fully dynamic registry for all IR

Rejected because it moves every operation to runtime completeness checking, adds indirect dispatch and metadata to the common path, and makes closed-world optimization/proof harder.

### 23.2 Ordinary wildcard for future variants

Rejected because it hides missing static cases—the exact defect class this plan targets.

### 23.3 Top-down runtime ID allocation

Rejected because load order changes serialized identity.

### 23.4 Automatically promote dynloaded variants into static ordinals

Rejected because artifact/cache/serialization ABI would depend on configuration. Keep persistent extension identity stable and only assign local dense tags after freeze.

### 23.5 `Any` as the generic implementation strategy

Rejected because Simple already has representation and engine-divergence evidence, and because it discards precisely the type/layout information needed for critical verification and optimization.

### 23.6 Late dynamic HIR in critical

Rejected because a future operation may lack an analysis/lowering/proof handler and invalidate already-verified assumptions.

### 23.7 Verify before aspect weaving

Rejected because advice changes control flow, effects, calls, generic instantiations, and unsafe obligations. Verify the post-weave program.

### 23.8 Hot unload in critical

Rejected initially because object/witness lifetime, active stack frames, code pointers, proof identity, and generation reclamation make sound unload a separate major problem.

### 23.9 Treat reports/TODO databases as completion evidence

Rejected. Only generated manifests and executable gates count.

---

## 24. Immediate implementation priorities

The first implementation sequence should be:

1. lock `CoverageState`, three semantic states, stable IDs, and Any unsafe rules;
2. build the generated schema/transition checker;
3. remove compiler silent fallbacks and wildcard coverage;
4. make current HIR→MIR type coverage explicit;
5. implement Any escape enforcement and canonical RuntimeValue conversion;
6. replace mono Any tables and implement real substitution/rewrite/post-check;
7. add closed/evolving sums;
8. add complete/dyn manifest and sealer;
9. integrate typed aspects before mono and post-weave verification;
10. close seed/self-host and engine parity;
11. migrate Simple packages to critical;
12. enable the aggregate release seal.

This ordering attacks the mechanisms that can make later work look green while being incomplete.

---

## 25. Research and repository references

### Repository sources inspected

1. [Mission-Critical Assurance Profile](https://github.com/ormastes/simple/blob/main/doc/02_requirements/language/mission_critical_profile.md)
2. [Unsafe-context enforcement port plan](https://github.com/ormastes/simple/blob/main/doc/09_report/unsafe_enforcement_port_plan_2026-07-27.md)
3. [Native-path monomorphization staged plan](https://github.com/ormastes/simple/blob/main/doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md)
4. [Current monomorphization integration](https://github.com/ormastes/simple/blob/main/src/compiler/40.mono/monomorphize_integration.spl)
5. [Current monomorphization engine](https://github.com/ormastes/simple/blob/main/src/compiler/40.mono/monomorphize/engine.spl)
6. [Current type substitution](https://github.com/ormastes/simple/blob/main/src/compiler/40.mono/monomorphize/type_subst.spl)
7. [Core type-erasure/mono support](https://github.com/ormastes/simple/blob/main/src/compiler/10.frontend/core/type_erasure.spl)
8. [Any slot holds untagged scalar bug](https://github.com/ormastes/simple/blob/main/doc/08_tracking/bug/any_slot_holds_untagged_scalar_2026-08-05.md)
9. [Any+Any native divergence state](https://github.com/ormastes/simple/blob/main/.spipe/any-any-native-divergence/state.md)
10. [Spawn/await/yield FlatAst silent NilLit bug](https://github.com/ormastes/simple/blob/main/doc/08_tracking/bug/spawn_call_expr_silently_becomes_nillit_2026-07-29.md)
11. [MIR lowering missing HirTypeKind arms](https://github.com/ormastes/simple/blob/main/doc/08_tracking/bug/mir_lowering_missing_hirtypekind_arms_wildcard_fatal_2026-08-05.md)
12. [Resolved match coverage](https://github.com/ormastes/simple/blob/main/src/compiler/20.hir/match_coverage.spl)
13. [Safety checker](https://github.com/ormastes/simple/blob/main/src/compiler/35.semantics/safety_checker.spl)
14. [HIR pipeline passes](https://github.com/ormastes/simple/blob/main/src/compiler/80.driver/driver_hir_pipeline_passes.spl)
15. [Aspect/facet dynload design](https://github.com/ormastes/simple/blob/main/doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md)
16. [Aspect-pack implementation coverage](https://github.com/ormastes/simple/blob/main/doc/09_report/aspect_pack_design_coverage_2026-08-18.md)
17. [Mission-critical parallel-agent plan](https://github.com/ormastes/simple/blob/main/doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md)
18. [Parallel ownership skill](https://github.com/ormastes/simple/blob/main/.agents/skills/parallel-ownership/SKILL.md)

### External primary research and official documentation

19. Najd and Peyton Jones, [Trees That Grow](https://arxiv.org/abs/1610.04799)
20. MLIR, [Defining Dialects](https://mlir.llvm.org/docs/DefiningDialects/)
21. MLIR, [Interfaces](https://mlir.llvm.org/docs/Interfaces/)
22. MLIR, [Operation Definition Specification](https://mlir.llvm.org/docs/DefiningDialects/Operations/)
23. Rust, [`std::any::Any`](https://doc.rust-lang.org/stable/std/any/trait.Any.html)
24. Rust Reference, [Unsafety](https://doc.rust-lang.org/stable/reference/unsafety.html)
25. Rust Reference, [`unsafe` keyword](https://doc.rust-lang.org/stable/reference/unsafe-keyword.html)
26. Rust Reference, [`non_exhaustive`](https://doc.rust-lang.org/reference/attributes/type_system.html)
27. Rust Reference, [Enumerated types](https://doc.rust-lang.org/nightly/reference/types/enum.html)
28. rustc, [Monomorphization collector](https://doc.rust-lang.org/stable/nightly-rustc/rustc_monomorphize/collector/index.html)
29. SPARK Reference Manual, [Representation Issues and Unchecked Type Conversions](https://docs.adacore.com/spark2014-docs/html/lrm/representation-issues.html)
30. Linux kernel, [eBPF verifier](https://docs.kernel.org/6.14/bpf/verifier.html)
31. Linux kernel, [Static Keys](https://docs.kernel.org/staging/static-keys.html)
32. OSGi Core, [Lifecycle and Lazy Activation](https://docs.osgi.org/specification/osgi.core/7.0.0/framework.lifecycle.html)
33. AspectJ, [Load-time Weaving Requirements](https://eclipse.dev/aspectj/doc/released/devguide/ltw-rules.html)

---

## 26. Final architectural statement

Simple should not choose between completeness and dynload.

It should preserve the strongest proof available at each boundary:

```text
static:
    compile-time exhaustive

complete:
    configuration/seal-time exhaustive

dyn:
    locally verified but globally open
```

Critical execution then admits only:

```text
static + sealed complete
```

`Any` is treated as an unsafe representation escape, generics become concrete through typed monomorphization, finite dynamic domains become closed sum types, compiler transitions become total generated relations, and aspects become part of the post-weave verified artifact identity.

That combination provides maximum practical completeness without imposing dynamic lookup, extra node fields, or erased representations on the common static compiler path.

## 27. Execution status (living — update on every change)

**This is the SINGLE status table for the bootstrap/hardening goal — every lane appends its row here, not in `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md` (that file tracks phase/lane scope only and points here for status).**

**Rule:** every landed lane commit touching this plan's scope appends a dated row to the table below *in the same commit*. A landing without a row here is incomplete.

| date | phase/lane | commit | what changed | plan section affected | evidence |
|---|---|---|---|---|---|
| 2026-08-21 | hardening lanes | `c089809a253` | compiler completeness lanes, bootstrap pinning, seed fixes, test sweep repairs | §20 | commit |
| 2026-08-21 | test-runner | `7a6f6459a81` | daemon backlog bypass; single-worker daemon serialized concurrent `simple test` | §20 (tooling) | `light_test_daemon_serializes_concurrent_test_invocations_2026-08-21.md` |
| 2026-08-21 | jit | `20416a1bda7` | optional class unwrap emitted enum payload read, segfaulting on field access | §20 (JIT completeness) | commit |
| 2026-08-21 | pure-simple | `73cd50caf97` | ForceUnwrap in tree-walk eval; matrix cases isolated per process | §20 | `pure_mir_force_unwrap_class_receiver_unresolved_2026-08-22.md` |
| 2026-08-23 | frontend / stage1 closure | `7f1d739455f` | an unmarked struct/class field is PUBLIC, not module-private: the flat-AST bridge fabricated `Visibility.Private` for every field, and the flat AST carries no per-field visibility at all, so no source marker could ever override it; HIR then denied every cross-module field read and aggregate construction (1512 errors across 44 files, rc=1 at step 2/6, on the real 140-module `src/app/lint` entry closure). Policy engine `member_visibility.spl` UNCHANGED. Same-class sweep: treesitter enum struct-variant fields. | §20 | spec `test/01_unit/compiler/frontend/struct_field_default_visibility_spec.spl` 3 failed pre-fix -> 3 passed post-fix (verified by reverting the bridge edit alone); record `hir_cross_module_field_visibility_blocks_lint_closure_2026-08-23.md`. Post-fix 140-module closure re-measurement STILL RUNNING under host contention (closure size reconfirmed 140; parse 5/140 after ~3h) — the post-fix error count at real closure scale is NOT yet established. |
| 2026-08-21 | mir | `7d5e33c9007` | closure conversion for capturing lambdas on the native path | §20 (MIR) | `native_capturing_lambda_closure_conversion_2026-08-22.md` |
| 2026-08-21 | hir | `144f608f81a` | package-sibling fallback for imported callable signature dependencies | §20 (HIR) | `hir_sibling_impl_signature_package_dependency_2026-08-22.md` |
| 2026-08-21 | seed perf | `d30727e74e3` | interpreter hot path: lazy coverage file per decision, shadow capture order, CowEnv frame maps on ahash | Phase 1 | `seed_interpreter_stall_profile_2026-08-21.md` |
| 2026-08-21 | hir perf | `88146e0e7e5` | NAMEIDX per-surface name index, SCOPEROW in-place scope probe, EXCL exclusive profile slots, PROFOFF fast path | Phase 1 / §20 (HIR) | `hir_phase_per_module_cost_2026-08-21.md` |
| 2026-08-21 | native-build | `a6233953eca` | HIR shard children re-parsed the closure — front-end cache scope split by entrypoint script | Phase 1 | `hir_shard_children_reparse_closure_2026-08-22.md` |
| 2026-08-22 | mono (#158 Phase C) | `43ead88be55` | generic class + generic impl declaration fatals replaced by non-emittable templating; MIR skips `is_generic_template`; unblocks the 3 stage1-closure sites in `async/{future,poll}.spl` (0 instantiations in the closure) | §9.3 step 12 | `generic_class_and_impl_declaration_gates_block_stage1_closure_2026-08-22.md` |
| 2026-08-22 | hir / native-build | `9980264a973` | `module_surface_projected_type_shape` / `_type_name` were called by 50feb3ba227 but never defined — every `--hir-shard` child died E1002 at `surface_build 5/687` (run11b); definitions added | Phase 1 / §20 (HIR) | `module_surface_projected_type_shape_undefined_e1002_2026-08-22.md` |
| 2026-08-23 | hir | `038b379541f` | bare-export package-sibling chase deduped owners against the LAST match only; A,B,A ordering counted 3 owners for 2 — replaced with a distinct-index set | §20 (HIR) | `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md` (incl. why no pre-fix-red fixture is constructible) |
| 2026-08-23 | assessment (dual impl) | (this commit) | measured that the 21,208 `*_spec.spl` files ALREADY run only on the Rust seed's tree-walk interpreter; `--mode=native` cannot compile the harness (E1002); BDD verbs are Rust intrinsics (`interpreter_call/bdd.rs:619`); owned `#[test]` is 10,246 not 45,488 (77% vendored); no coverage tooling in owned code | §20 / §27 | `doc/01_research/compiler/dual_impl_test_sharing_assessment_2026-08-23.md` |
| 2026-08-23 | testing docs | `e3492e48476` | `@tag:in-development` documented across guides + skills (testing guide, test-helpers QR, spipe skill, sp_dev, sstack-spec plugin, structure rules, test_runner layer wiki, new `test_in_development_tag` feature wiki): semantics (expected FAIL / skipped in whole-suite / **counted** in summary / `--tag in-development`), promotion rule, and the anti-use boundary (never a regression, an undiagnosed failure, or an unavailable host). Enforcement status stated honestly: `--tag` exists in the seed driver (`args.rs:24`, `execution.rs:923-925`) and `@tag:qemu` is scanned at `execution.rs:95`, but the pure-Simple runner parses only `@di_test`/`@exec_limit` (`test_runner_single.spl:193,209`) — a tagged spec today still runs and still fails | §20 (tooling) | `doc/07_guide/infra/testing.md` § Tags and Filtering; grep of `origin/main` @ `3ccf808f6f2` for `in-development` in `src/` = 0 hits |
| 2026-08-23 | mono (§9.4) | `75f554903ff` | type args are now inferred from MATCH-ARM payload bindings and FOR-LOOP variables, not only params/`let`s; enums are collected for their declared payload types. 67 of the ~76 real root generic call sites in the whole stage1 closure are match-arm bindings (all in `20.hir/generated/hir_hash.spl` calling `_hir_mix_prim<T>`), so every one raised E-MONO-032 -> E-MONO-033 and step 3/6 could never pass. Fail-closed preserved: nothing inferable is left unbound rather than guessed | §9.4 | `generic_class_and_impl_declaration_gates_block_stage1_closure_2026-08-22.md`; spec `mono_pattern_bound_type_arg_inference_spec.spl`; fixture f13 (closure size 1) pre-fix `unresolved=2` + E-MONO-033 at step 3/6, post-fix `specializations=2 unresolved=0` and **step 6/6 rc=0 linked** — steps 3/4/5/6 all now execute |
| 2026-08-23 | hir (#158 Phase C) | `75f554903ff` | generic STRUCT declaration fatal replaced by non-emittable templating, matching the class/impl precedent `43ead88be55`. Enumerated, not assumed: `src/compiler`, `src/runtime` and `src/app/cli` declare ZERO generic structs and import none of the 28 under `src/lib`, so the stage1 closure has no instantiation to mislower. Corollary: the phase36 forecast's item 3 is wrong for stage1 — this gate blocked fixtures f01/f12, not the closure | §9.3 step 12 | same record; fixture f01 (closure size 1) pre-fix `hir-fatal: generic structs are not supported...` at step 2/6, post-fix HIR+mono clean and **reaches step 4/6 MIR**, where it meets the still-open struct-instantiation gap (`unresolved method call: to_text`) — a loud MIR error, not the silent truncation the old gate feared |
| 2026-08-23 | hir / guards | `0fe0323565c` | re-landed the type-walk constructor-parity guard ALONE after it was lost as collateral damage of the `ec13c319250` revert (it had been bundled into the fix commit `d481f15e1ac`); its first honest run caught a genuinely stale `Function` allowlist line | §20 (HIR) | `hir_unresolved_type_owner_missing_import_2026-08-22.md` follow-up (f); `PASS — 11 constructor(s) checked` |
| 2026-08-23 | seed memory / interpreter write-back | `1c3f314ad4610d83b4956fcab91faa036bc5e74f` | **`f(obj.field)` write-back copy-on-wrote the caller object's whole field map against a DEAD alias, on every call.** `outer_env.get(&name).cloned()` leaves the frame holding the same `Arc`, so `Arc::make_mut` was *guaranteed* to deep-copy even though the binding is overwritten two lines later and the frame is suspended. Counter pin `FIELD_WRITEBACK_MAP_CLONES`: **200/200 pre-fix -> 0 post-fix**. Class swept: the value-type-struct merge branch (`function_exec.rs`) and the lambda `obj.field` twin (`lambda.rs`) had the identical shape and are fixed in the same commit. New `CowEnv::take_frame_owned` / `restore_frame_owned` fire ONLY when the frame is the value's sole home, so a live alias (shared base/scope layer) still copies -- value semantics unchanged | §27 (seed memory) | `seed_field_writeback_copies_object_map_against_dead_alias_2026-08-23.md`; `compiler/tests/interpreter_field_writeback_no_dead_alias_copy.rs` (FAILS pre-fix: "field map copied 200 times across 200 write-backs"); perf-gate rows `field write-back: *` |
| 2026-08-23 | seed memory / CowEnv | `1c3f314ad4610d83b4956fcab91faa036bc5e74f` | **every call frame heap-allocated its own EMPTY `global_bindings` map** (`Arc::new(HashMap::new())` at four `CowEnv` sites). Sibling of `7fe00b1c4d5`, whose own doc comment named this inner `Arc<HashMap>` as part of the waste it was accounting for but only shared the OUTER `CowEnv` -- the instance-not-class case. Now one thread-local shared empty; every mutation already routes through `Arc::make_mut`, so an empty map has no observable identity | §27 (seed memory) | `seed_empty_global_bindings_map_allocated_per_frame_2026-08-23.md`; `compiler/tests/interpreter_shared_empty_global_bindings.rs` (holder-count pin + a COW guard proving a real binding does not leak to siblings); perf-gate rows `shared empty global_bindings: *` |
| 2026-08-23 | build parallelism / worker memory | `ff095d31591116e99541a7c115bb53518f6cb8f3` | **shard concurrency was derived from CPU count alone and was killing runs, not merely costing memory.** `bootstrap-from-scratch.sh` picks `host_cpus/2` = 16 here; a measured worker holds 2.40-2.74 GB RSS (VmPeak 3.37 GB, 99.4% anon, `Pss ~= Rss` -- only ~14 MB shared across 8 workers), so one run asked for ~40 GB and the worker group was OOM-reaped mid-HIR (run17 `rc=255` after 12,643 s / 3 attempts, death points 13/688, 288/688, 509/688 -- flaky, not a compiler defect). No backoff existed: `check-heavy-work-preflight.shs` is a one-shot admission gate that refuses to start and never lowers N. Fix clamps to `floor(MemAvailable * 0.6 / worker_budget)` with **per-phase** budgets -- parse shards 1.65 GB (slim entry), HIR shards 3.0 GB (still the full worker closure) so HIR is clamped harder. Measured at MemAvailable 21,958,928 kB, request 16: parse **16 -> 7** (26 -> 11.6 GB), HIR **16 -> 4** (48 -> 12 GB). Safe by construction: shard phases are a cache warm-up, output identical at any N; only ever reduces, never 0, no-ops on unreadable MemAvailable, one-shot at spawn (a mid-run loop would re-open the orphaned-claim class fixed by `6cedd51faec`) | §27 (build parallelism) | `shard_threads_no_memavailable_clamp_2026-08-23.md`; `test/01_unit/app/cli/shard_mem_clamp_spec.spl` (7 ex / 455 ms; neuter check: `cap = requested` turns 3 of 7 red); perf-gate rows `SHARDCLAMP *`; limits doc `doc/09_report/rust-perf-limits.md` |
| 2026-08-23 | architecture-level perf limits (new canonical doc) | `ff095d31591116e99541a7c115bb53518f6cb8f3` | opened **`doc/09_report/rust-perf-limits.md`** as the ONE place recording perf/memory limits unreachable within the minimal-semantics-preserving-edit constraint, so they are reported rather than forced or silently skipped. Seeded with L1 process-per-worker shares nothing (`Pss ~= Rss`, 14 MB / 8 workers; fix needs fork-after-closure or mmap'd shared source, est. **10-18 GB per build**), L2 monotone RSS 2.40 -> 2.74 GB never released + one 2,450 MB mimalloc arena (retention is process-immortal *by design* -- frozen surfaces, SoA source text, duplicate `ctx.sources` inventory, non-shrinking AST arena; only the allocator purge tunable is non-architectural), L3 full closure source retained in every worker (the shard queue is *dynamic*, so a static filter is incorrect not merely suboptimal), L5 fixed startup does not shrink with N, L6 link is 93% of back-end wall and its **RSS is still unmeasured**, L7 interpreter family ~92k LOC is a floor on closure size. Targets recorded: compile < 1 GB (currently 2.4-2.7 GB, **not met**, gap is L1-L3), link < 3 GB (**unverified**). Other lanes append here rather than opening parallel reports | §27 | `doc/09_report/rust-perf-limits.md`; `doc/09_report/build_parallelism_memory_audit_2026-08-23.md` |
| 2026-08-23 | seed memory / arg binding | `1c3f314ad4610d83b4956fcab91faa036bc5e74f` | per-call `Vec<String>` of every parameter name built for a diagnostic gated behind `SIMPLE_DEBUG_ARG_BINDING` (off by default); moved onto the error path and switched to `&str`, and `bound` now reserves its known size. Real-workload effect of the three fixes together, identical command both sides (`bootstrap_main compile 20.hir/hir_lowering/module_surface_registry.spl`): peak RSS **2,352,152 KB -> 2,308,256 KB**, wall 2:16 -> 2:05 -- the counter pins, not this delta, are the mechanism evidence, since that workload is dominated by module loading | §27 (seed memory) | perf-gate row `arg binding: debug param-name Vec not built per call` |
| 2026-08-23 | twin check (negative) | `1c3f314ad4610d83b4956fcab91faa036bc5e74f` | the C runtime's tombstones-counted-toward-load-factor dict bug (`e24b2845b3b`) has **NO twin in the Rust runtime**: `runtime/src/value/dict.rs` `rt_dict_remove` uses backward-shift deletion (it rehashes the rest of the probe chain into the hole) and decrements `len`; the word "tombstone" does not appear in the file, so the 3/4 grow test at `dict.rs:258` measures live entries, not churn. Recorded so the negative is not re-investigated | §27 (process) | `seed_field_writeback_copies_object_map_against_dead_alias_2026-08-23.md` § Twin check |
| 2026-08-23 | compiler / frontend | `d82a9a5021d` | `frontend.spl:134` called `TreeSitter.new(authority_source)`. `TreeSitter` is a 15-field `struct` with no hand-written static `new`, so the synthesized constructor takes all 15 fields and a 1-arg `.new` matched no candidate — every `native-build --entry-closure` reaching `10.frontend` died in semantic analysis with `unknown static method new on class TreeSitter` **before lowering**, so those runs reported zero `[hir-fatal]` lines because they never got there, not because they were clean. Killed every `--source src/compiler` oracle at step 1 (stage1 itself, `--source src/app`, is unaffected). Introduced by `b9f1be59f8c`. Fix: call the real 1-arg constructor, the free fn `treesitter_new(source)`. Three rival diagnoses were killed BY MEASUREMENT, not inspection: an `export use` provenance gap at `outline.spl:23` (changing it altered nothing; importing `TreeSitter` straight from its declaring module still failed identically), a half-landed optional-field desugar at the three `TreeSitter(...)` literal sites (supplying all 15 fields changed nothing — real but latent debt), and a missing class (it exists, single decl). Spec landed separately as `07d2e40a7e1`. **Next abort now exposed, same blocker class, still open:** `method `is_at_end` not found on type `TreeSitter`` | §27 (compiler) | `treesitter_new_static_method_missing_2026-08-23.md` |
| 2026-08-23 | compiler / frontend + mir_opt + linker | `d6fce96e530` | The abort `d82a9a5021d` uncovered: `fn treesitter_is_at_end(self: TreeSitter)` (`outline_lexer.spl:178`) was called as `self.is_at_end()` at 20+ sites, so every `native-build --entry-closure` reaching `10.frontend` died with ``method `is_at_end` not found on type `TreeSitter```. Two facts settled BY MEASUREMENT, and they cut against how the message reads: (1) **UFCS is real** — a free `fn f(self: T)` IS callable as `x.f()`, and resolves ACROSS modules *without importing `f`* (the type carries it), so the siblings' bare `use ...outline_lexer.{TreeSitter}` was never the problem and the fix needed no new `use` lines; (2) **there is no type-prefix stripping** — `x.get()` against `box_get(self: Box)` fails identically for BOTH `me` and `fn`, so `me` vs `fn` is irrelevant to method resolution and the earlier 'declared `fn` not `me`' framing is a killed red herring. The declared name IS the method name: the language is right, the call sites were wrong, written as if a lowercased-type-prefix-stripping rule existed. Fix: call the declared names. Declarations deliberately NOT renamed to the stripped forms — they are module-scope free functions whose type prefix is what keeps `parse_identifier`/`advance`/`error`/`check` from colliding across the package, so that would trade a resolution defect for a namespace collision. **Class sweep tree-wide:** of 18,828 `me` decls only 86 take an explicit `self:` param (the normal style is implicit self inside a type body); 39 files use the shape; exactly 7 called the stripped name — **579 sites**: outline.spl 185, outline_members.spl 159, outline_decls.spl 151, outline_types.spl 48, outline_lexer.spl 20 (all `treesitter_`), copy_prop.spl 15 (`copypropagation_`), lazy_instantiator.spl 1 (`lazyinstantiator_`). Rewrite is type-scoped (prefix = lowercased *sole* `self:` type of the file, target must be declared `self: T`), hence 1:1 and line-count neutral (568+/568-); a looser suffix-only heuristic gave 114 hits incl. a false positive at `safety_checker_transfer.spl` (`self.error()` matching `treesitter_error`), which is why the applied rule is type-scoped. 4 multi-self-type files skipped by that rule and inspected as non-offenders. Spec landed separately as `7dd1fafaae8` (RED 3 of 4 pre-fix, 4/4 post-fix; the one example green on both sides is the behavioural UFCS proof, labelled as such, not a reproducer). | §27 (compiler) | `treesitter_new_static_method_missing_2026-08-23.md` (extended in place, not a parallel narrative) |
| 2026-08-23 | guards / enforcement | `b2de1a33e27` | **R1 of the guard-vacuity audit closed.** `.claude/rules/vcs.md` stated verbatim that a set of guards were "Wired into `pre-push-conflict-tree-guard.shs`" and called several MANDATORY; they appeared in **no** enforcement surface. The hook runs no guards itself — it `exec`s `check-push-must-pass.shs`, which executes exactly the `push`-tier rows of `config/check/must_check_gates.sdn` (five of them). Eight guards were measured on `origin/main` and wired as blocking push rows: `check-runtime-api-regression-push`, `check-c-runtime-compiles-push` (25s), `check-no-direct-rt` (8s), `check-signature-type-import-provenance` (7s), `check-type-walk-constructor-parity`, `check-perf-regression-tests`, `check-process-wait-eintr-retry`, `check-guard-wiring` (39s) — total ~90s, each verdict line observed by feeding a real ref row to the driver, not by name-matching a file. `push_blocking` was parsed and then IGNORED, so the only two states a guard could hold were "blocks every push" and "runs nowhere", which is precisely why the slow and honestly-RED ones held neither; `run_push_gate` now honours it and an advisory verdict is RECORDED on stderr, never silent, never a pass. Six guards were NOT wired and the doc now says so with the measured reason each (RED: `check-core-lib-purity` 18 new violations, `check-seed-extern-registry` 2 new unregistered; ERROR without a deployed compiler or stage artifacts: `check-bodyless-block-parity`, `check-unbacked-extern-ratchet`, `check-stage-binaries-runnable`; too costly: `check-cow-alias-hotpath` 226s; `check-seed-builds-push` needs a warm cargo dir). Meta-guard `check-guard-wiring.shs` went from a permanently-RED `FAIL — 414 unwired` (ignored for weeks, so a NEW unwired guard was indistinguishable from the backlog) to `PASS — 871 guard(s) checked, 0 NEW unwired`: the 400 remaining are frozen in `scripts/check/guard_wiring_unwired_baseline.txt`, deliberately NOT the opt-out file (an opt-out asserts "not a gate"; a baseline asserts "unwired debt, known"), growth fails, and an entry that becomes wired or vanishes fails as stale, making regeneration deletions-only | §27 (guards) | `doc/09_report/guard_vacuity_audit_2026-08-23.md` R1 |
| 2026-08-23 | guards / perf | `2989e1f3ffe` | **`check-perf-regression-tests.shs` was clobbered by `e24b2845b3b`** — a stale-base rewrite that took it from 116 mechanism rows to 68, silently unpinning ~50 landed perf fixes (`ANYVTJIT`, `FNREFJIT`, `GLBMEMO`, `HIRCODECCHUNK`, `HOPPARK`, `QTYPEIDX`, `SCALARARR`, global-push, lexer `source_chars`). Same defect class as the parse-shard revert: protection removed while everyone assumed it existed. The 50 lost rows were recovered from `50a379f83b7` and **UNIONed** with everything later lanes appended (81 rows at origin), never replaced; result 131 rows, **all green**, so no restored row exposed a real regression. Added `ROW_FLOOR`: the guard now FAILs when its own row count drops below the recorded floor, making the class self-detecting instead of depending on someone noticing a smaller number | §27 (guards) | clobbering commit `e24b2845b3b` |
| 2026-08-23 | process rule | `0fe0323565c` | **guards land in their OWN commit** — a guard sharing a commit with the fix it guards is deleted by any revert of that fix, and the bug record goes on claiming enforcement that no longer exists (this is how the parity guard was absent for a day). Applies equally to baseline/allowlist files | §27 (process) | same |
| 2026-08-23 | guards / perf (COW) | `50a379f83b7` | the COW-alias ratchet hardcoded `SRC="$ROOT/src/compiler"` and scanned **only** the compiler tree, so `src/lib` — 7,864 `.spl` files, 83% of the owned tree — was never scanned at all: it reported `PASS ... 7 offender(s)` while the tree carried **219**, and its verdict line gave no hint it wasn't looking. `scan()` now takes a path prefix and runs over both trees (lib rows prefixed `lib/` so they cannot collide); 0 files under EITHER tree is ERROR, never a pass; a 9th selftest fixture pins the prefixed scan so deleting the second call cannot silently restore the blind spot. Baseline regenerated (reviewed): `PASS — 9674 file(s) scanned, ... 198 offender(s)` = 7 compiler + 191 lib | §27 (guards) | `cow_alias_ratchet_blind_to_src_lib_2026-08-23.md`; perf-gate rows `COWLIB` |
| 2026-08-23 | lib / perf (COW) | `294571af220` | JS VM object store (`vm_object_store.spl`) took a `var` alias of **seven** parallel property arrays in `set_property`, `set_reference_property` and `remove_property`, then stored them back — the canonical COW-ROUNDTRIP. The alias holds `strong_count` at 2 across every write, so `Arc::make_mut` deep-copied each WHOLE array: seven copies on the append path, three more on the in-place-update path (an indexed write through the alias is itself a whole-array copy). The store is a **global** append-only property log, so those arrays are sized by every property of every live object in the heap, making each property write O(P) and object/array construction O(P^2) — and `set_property` is the VM's hottest path (every JS property write, every array element store, the `create_array_from` loop). Fixed by mutating through the single owner; semantics-preserving, since no other live binding observes those fields between the alias and the store-back. `simple lint` clean | §27 (perf) | `cow_alias_ratchet_blind_to_src_lib_2026-08-23.md`; perf-gate rows `COWLIB` |
| 2026-08-23 | testing / test-runner | `be0213e30ea` | **The in-development tag had a hole that a tree-wide tagging sweep would have turned into hidden debt at scale.** A spec carrying `@tag:in-development` that failed to LOAD — syntax error, broken import, unresolvable module — produced `executed=0`, classified as `ExpectedFailure`, and was neutralised into a silent counted skip, **indistinguishable from a spec whose subject merely does not work yet**. Filed as a known limit when first found; promoted to a fix because three lanes are now tagging ~21,000 specs (`test/01_unit`+`unit` 13,942, `test/03_system`+`system` 5,323, `test/02_integration`+`integration`+`feature` 1,720), at which scale it is exactly the protection-that-hides-debt shape. Fix: third class `InDevelopmentOutcome.LoadFailure`, checked BEFORE the failure branch, discriminated by the runner's **existing** `is_load_failure(error)` — precisely `unrun_reason(error) != "zero-examples"`, so no new predicate was invented. **It still FAILS the run, deliberately:** `@tag:in-development` is a claim about the CODE UNDER TEST, not about the spec file; a spec that cannot be loaded is a defect in the SPEC, and one no assertion inside it can ever be reached to demonstrate — the tag buys amnesty for failing ASSERTIONS, never for a file the loader could not read, or it becomes a place broken files go to stop being counted. The obvious counter-argument (a WIP spec legitimately importing a module that does not exist yet) was considered and REJECTED: textually identical to a typo, so honouring it re-opens the hole; the remedy is cheap and explicit (stub the import, or do not tag until it loads). **Decision 5 intact** — a file that LOADS cleanly and simply declares no examples is not broken, stays `ExpectedFailure`, and still never announces itself ready to promote. Mechanically the result is returned essentially UNCHANGED (`error` preserved, so `emit_spec_file_verdicts` still routes it through `unrun_verdict_line` and the existing greenwash gates still see it) with `failed` forced to >=1. **Latent bug fixed on the way:** the first cut cleared `error` BEFORE anything could inspect it, so `emit_spec_file_verdicts`' own `is_load_failure(r.error)` test was already blind and every broken tagged spec printed a bare `outcome=NOT_RUN`. API for the sibling lanes widened: `in_development_totals` returns THREE buckets `(skipped, unexpected, broken)`, `classify_in_development` takes a sixth `load_failed`, `in_development_summary_line` takes `broken`, plus `IN_DEVELOPMENT_BROKEN_MARKER` / `in_development_broken_line` — **the stats lane needs a matching BROKEN bucket** in `bin/simple tags` and the `test_result.md` In Development row, or it re-creates the same absorption there. Measured end to end on a sweep of one broken + one merely-failing tagged fixture: `IN-DEVELOPMENT BROKEN ... (unresolved-module)` + `IN-DEVELOPMENT SKIP ... (1 expected failure(s))`, `Results: 1 total, 0 passed, 1 failed, 1 skipped`, `In-development: 1 skipped (expected to fail), 1 BROKEN (failed to load — FAILS the run)`, and **no `All tests passed!`**. Spec landed separately as `9051e879d1d` (28 examples, up from 21). Design doc now also states that **tagging is only safe for load-clean specs**, so sweep reports are read correctly | §27 (testing) | `doc/05_design/app/testing/in_development_tag.md` Decision 7 |
| 2026-08-23 | testing / test-runner | `970920e02cd` | **A test for code that isn't finished had nowhere to live.** Landing it red made the suite verdict useless; not landing it meant writing it twice; `skip()`-ing it made the debt INVISIBLE, which is how a "temporary" WIP test becomes a dead file nobody remembers. New file-level tag `# @tag:in-development` declares a spec WORK IN PROGRESS and EXPECTED TO FAIL. Built on the EXISTING `@tag:<name>` source-comment channel, not a parallel scheme — censused first: **57 distinct tag names, 1022 occurrences** across `src/`+`test/`, and multi-word names in that census are **already hyphenated** (`back-compat`, `api-individual`, `evidence-source-contract`), so `in-development` is the convention and `in_development` would have been the deviation. `pending` / `skip` were deliberately NOT reused (a `pending()` example ran nothing; `skip()` is a claim about the HOST, not the code under test), and `wip` has zero occurrences. `SkipCondition.tags: [text]` (`condition.spl:43`) was surveyed and left alone — it is **dead**: no `matches_tags` exists, `create_skip_condition` stores it and nothing reads it, so reviving it would have rested a live feature on machinery that has never run. **Semantics, each decided explicitly:** sweep+fail -> neutralised, but COUNTED and PRINTED (`IN-DEVELOPMENT SKIP` per file, `In-development: N skipped` in the summary, not behind `--verbose`); sweep+pass -> `IN-DEVELOPMENT UNEXPECTED PASS ... ready to promote`, loud but NOT converted into a failure (failing the suite on good news creates pressure to delete the tag before landing the fix, losing the signal); explicit path -> honest red, normal exit code, because a neutralised explicit run makes a WIP test impossible to iterate on — and a DIRECTORY target is a sweep, not explicit, or nearly every real invocation would go honest-red and defeat the feature; crash/timeout folded into the same neutral path so a segfaulting WIP spec cannot escape through the error channel; zero-examples classifies as expected failure, never a promotion signal, so an empty file cannot announce itself ready. **"Skip" here means skipped from the VERDICT, not from EXECUTION** — the file still runs, because a file that is never executed can never be observed to have started passing, which would make promotion detection unimplementable and let WIP tests rot forever. **No sibling lane's file was touched:** explicit targeting reuses the already-existing `TestOptions.path_explicit`+`paths`, and the neutralised `TestFileResult` shape (`passed=0 failed=0 skipped>0`) stays recoverable by `in_development_totals` re-reading the tag, so no new struct field was needed and daemon/cache-replay results still classify correctly. Library layer is PURE (text in, verdict out, no externs) so it adds no direct `rt_*` call site to the ratchet; neutralisation is applied at the single point every execution mode funnels through. Measured: sweep of 1 failing + 1 passing tagged fixture -> `All tests passed!` + `In-development: 1 skipped (expected to fail), 1 UNEXPECTED PASS (ready to promote)`; explicit path -> `FAIL`, rc=1; unit spec 21/21 (pre-fix `outcome=ERROR executed=0`). **Two limits stated rather than papered over:** the aggregate `SPEC FILE VERDICT:` line for a neutralised file reads `outcome=NOT_RUN` (cosmetic — `test_file_result_outcome_class` counts `skipped` toward examples so the exit code is `OK`; a first-class in-development outcome needs the `light_protocol`/`test_runner_types` lanes' agreement), and a CONTROL sweep of untagged passing specs reproduces a **pre-existing** post-run `error[E1002]: function `runtime_file_rename` not found` rc=1, recorded so the measurements above cannot be misread as caused by this change. Specs land separately | §27 (testing) | `doc/05_design/app/testing/in_development_tag.md`; guide `doc/07_guide/testing/in_development_tag.md` |
| 2026-08-23 | backend / correctness | `f17b8afc66a` | **codegen FAILED OPEN.** `MirToLlvm.emit_unsupported_panic` emitted a `call void @rt_panic(...)` INTO THE GENERATED IR and returned normally, so a program using any of the 33 `MirInstKind` variants with no LLVM arm built **rc=0, step 6/6, linked** — and died at RUN time. Measured live: an ordinary `Result<i64,text>` + `?` program linked green then panicked `E-BACKEND-LLVM-INST-ResultMatchSemantic`. Lane C7 had already named these codes; what it did not change is WHEN the failure lands. Now a compile error naming the kind and site (matching DecisionProbe/ConditionProbe, which already panicked at COMPILE time); `SIMPLE_ALLOW_UNLOWERED_MIR=1` restores the old behaviour. Twin fixed identically: `CBackendTranslate.emit_unsupported_panic` (~40 sites) emitted `spl_panic(...)` into the generated C. Does NOT implement any of the 33 kinds — `Result` + `?` now fails loudly where it shipped dead | §27 (correctness) | `llvm_backend_unlowered_mir_kind_fails_open_2026-08-23.md` |
| 2026-08-23 | guards / backend | `b2176a58660` | own-commit gate for the row above: builds the incident fixture with `native-build` and FAILs on either a green rc with a dead/wrong binary, or a failing build with no named `E-BACKEND-LLVM-INST-*` diagnostic. Fatal selftest first; 0 fixtures built / missing compiler / timed-out build are all ERROR, never a pass | §27 (guards) | same |
| 2026-08-23 | backend / class sweep | (filed) | the same fail-open mechanism exists in **7 more backends**, 5 of them fully SILENT (instruction dropped, no diagnostic): Cranelift adapter `cranelift_codegen_adapter.spl:761` (`case _: ()`, "skip silently for now", JIT/AOT path), the SHARED base trait `common/mir_text_codegen.spl:289` (every non-overriding subclass inherits it), `llvm_lib_translate_expr.spl:225`, `wasm/wat_codegen.spl:393`, `opencl_backend.spl:346`; plus runtime-trap-only `lua_backend.spl:310` and `native/isel_riscv64.spl:343`. Deliberately NOT changed with the fix — a hard failure on the JIT path could surface breakage in unexercised lanes. `exhaustiveness_validator.spl` exists to catch exactly this class and is evidently not run over those five; wiring it there is the ratchet | §27 (correctness) | same |
| 2026-08-23 | frontend / correctness | (filed) | **CORRECTS the phase36 forecast.** Fixture f06 was filed as a native codegen miscompile; it is not. `fn f() -> T?` reached through an IMPLICIT TAIL RETURN silently yields `nil` — bare identifier, parenthesised identifier, tail `if`/`else`, tail `match` all broken; explicit `return n`, explicit `Some(n)`, and an explicitly optional-typed local all work. Interpreter and native agree BYTE FOR BYTE across 5 forms, so an engine-differential comparison is clean and the defect is upstream of both. f06's "dropped `if r != nil` branch" is a consequence: `find(3)` really returns nil. Related: `-> Option<i64>` (generic spelling) returns a RAW unwrapped value (`<value:0xffffffffffffffff>`) because the seed's auto-`Some`-wrap gates on `Type::Optional` while `sffi_return_contract` classifies `Type::Generic{Option}` as optional — the two disagree. `Option` is the #1 unresolved name in the HIR census (1470) | §27 (correctness) | `implicit_optional_return_yields_nil_2026-08-23.md` |
| 2026-08-21 | bootstrap | `2fec447281f` | stabilize phase2 runtime and stage3 cache path | Phase 1 | commit |
| 2026-08-22 | native-build | `6cedd51faec` | log every parse-shard exit; reclaim a dead shard's orphaned queue claims | Phase 1 | `parse_shard_orphaned_claims_after_shard_death_2026-08-22.md` |
| 2026-08-22 | seed perf | `5ff4999c8e9` | scalar-element array args skip per-call value-type scan — interpreted lexing was quadratic in source | Phase 1 | `seed_interpreter_raw_throughput_2026-08-21.md` |
| 2026-08-22 | hir (many) | `66ccf79f57f`..`5d539f31e7e` | import-route freezing, signature owners, composite projections, span binding (≈25 `fix(hir)`/`fix(frontend)`/`fix(parser)` commits) | §20 (HIR/frontend) | `stage3_selfhost_imported_type_resolution_cascade_2026-08-21.md` |
| 2026-08-22 | sffi | `bae6d82891e`..`505a32265db` | Torch error preservation + typed failure sweep (≈14 `fix(sffi)` commits) | §20 (SFFI) | `sffi_non_optional_fallthrough_fabricates_nil_2026-08-21.md` |
| 2026-08-22 | checks | `09e879ff838`, `775fb38377a`, `cb2aef31d8e` | must-check ledger ownership, must-pass evidence bound to measured stage2 | §20 (gates) | `check_push_must_pass_requires_unobtainable_bootstrap_fingerprint_2026-08-22.md` |
| 2026-08-22 | audit | `f2761551931` | extern census made linear | §20 (tooling) | commit |
| 2026-08-22 | docs | `eb939043b96` | added §27 and §20 pointer | §20, §27 | — |
| 2026-08-22 | jit / seed symbols | `c0c4e707789` | last two stage1 JIT blockers. `rt_native_build` was defined only in the `staticlib` `native_all` crate, which nothing can link (`nm` seed = 0) — relocated into `simple-compiler::native_build_sffi` and registered by real address via `codegen::jit::COMPILER_OWNED_RUNTIME_SYMBOLS`; `native_all` re-exports it, so its archive symbol set is unchanged. `runtime_file_rename` was never a runtime symbol: it is the alias of `use std.io_runtime.{file_rename as runtime_file_rename}`, left unresolved because four modules define `file_rename` — HIR alias resolution now disambiguates on the flattener's module-owner tag. Sweep: 83 of 1831 `RUNTIME_SYMBOL_NAMES` are unresolvable from the seed, now ratcheted | Phase 1 / §20 (JIT, HIR) | `jit_unresolved_rt_native_build_and_runtime_file_rename_2026-08-22.md`; `compiler/tests/native_build_and_alias_symbols_registered.rs` |
| 2026-08-22 | hir perf / codec | `13bf3b2beee` | HIR per-module cliffs were `hir_module_encode`, not lowering: `HirCodecWriter.parts` was deep-cloned by the seed on every push (class reaching a frame through >1 parameter hop keeps a 2nd Arc owner), so encode was O(n²). Writer now accumulates into bounded chunks. zca_rows encode 1,139,353 ms -> 6,702 ms (170x), blob byte-identical | Phase 1 / §20 (HIR) | `hir_codec_writer_quadratic_cow_clone_2026-08-22.md` |
| 2026-08-22 | stage1-in-JIT / fn-ref ports (seed JIT) | `7a137dbffdb` | named-fn-as-value JIT-compiled via `name$boxed` thunk + zero-capture `rt_closure_new`; jit.rs guard narrowed to bodiless/extern names; dead uncompilable `declared_imported_surface_signature_type` removed (was the HIR-lowering gate). Stage1 STILL interprets: next gate `[CODEGEN-AMBIGUOUS-METHOD]` on `Any`/trait-object receivers (6 bodies: `BlockRegistry.register`, `register_block`, `with_block`, `objtaker_take_*`) | §20 | `doc/08_tracking/bug/jit_fn_ref_port_bails_whole_stage1_2026-08-22.md`, `tests/fn_ref_value_jit.rs`, perf-gate rows `FNREFJIT` |
| 2026-08-22 | hir names (run13) | `ead29e6df64` | run13 `unresolved name` class (60 occurrences / 24 pairs). Every symbol IS defined; the caller reached it only through a re-export edge that does not carry it — a plain `use X.*` (not a re-export), a barrel `export use Y.{...}` whose brace list omitted the name, a caller brace list omitting it, or a package `__init__` standing in for the defining module. The seed resolves all four leniently, which is why they accumulated invisibly. Diagnosis pinned by controlled comparison: `parser_type_kind_named_name` has 8 callers, the 7 with a direct import resolve, the 1 without is the only one that errors. Fixed at the import edges in 7 files — no resolver change, nothing silenced. Clears 42 of 60. The sibling `unresolved type` lane landed `1aa81cac8c6` mid-flight with byte-identical repairs for 2 of the 7 files (25 occurrences) — independent confirmation of the diagnosis; those were dropped here and the other 5 repairs verified still absent at that tip. 18 std/builtin/type occurrences deliberately left open (ambiguous provenance / sibling lane) | Phase 1 / §20 (HIR) | `hir_unresolved_name_import_reachability_2026-08-22.md`; `test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl` (pre-fix 0/6, post-fix 6/6) |
| 2026-08-22 | stage1-in-JIT / runtime symbols (seed JIT) | `0dc1ab047d5` | `rt_process_read_stdout_checked` + the whole C-only `rt_process_*_piped` family were listed in `RUNTIME_SYMBOL_NAMES` and defined in `src/runtime/runtime_process.c`, but `runtime/build.rs` never compiled or scanned that C file — so they got no `RuntimeSymbolEntry`, the JIT bound a NULL GOT slot, and `first_unresolved_import` dropped stage1 to the interpreter. build.rs now compiles `runtime_process.c` + `runtime_fork.c`; the three Rust-duplicated symbols are guarded out by `SIMPLE_RUNTIME_PROCESS_RUST_CORE` | §20 (JIT / SFFI) | `jit_unresolved_rt_process_read_stdout_checked_2026-08-22.md`, `tests/process_checked_symbols_registered.rs` |
| 2026-08-22 | hir perf / symbol table | `b8630a4b108` | QTYPEIDX: `SymbolTable.lookup_qualified_type_raw` linear-scanned three parallel arrays (2 text compares/row); `materialize_imported_callable_dependency` issues up to 3 probes per named type per imported callable per importing module, and 84% MISS (misses always pay full length) — 1,496,719 probes / 1,251,806 misses in run12, ~3.4 ms/probe, making `callable_deps` (5,241,657 ms) the largest exclusive HIR term. The `qualified_types` Dict was already maintained in lockstep by the only writer and is the only form the codec serializes; lookups now read it (key `module#member`, injective — `.` aliased ("a.b","c") onto ("a","b.c")). Write-only arrays deleted, removing an O(n²) CoW-push build too | Phase 1 / §20 (HIR) | `hir_qualified_type_lookup_linear_scan_2026-08-22.md`, `qualified_type_lookup_scaling_spec.spl`, perf-gate rows `QTYPEIDX`; measured `cse.spl` callable_deps 14,693 ms -> 401 ms (~37x), no longer the dominant term, with untouched `enums`/`functions` flat as the control |
| 2026-08-22 | hir perf / import lowering | `7f9a3e1c050` | GLBMEMO + QTYPEIDX follow-up measurement. **Measured** (controlled A/B, same `compile` invocation on `5c38b388a53` vs `5c38b388a53~1`, run concurrently, 16 matched modules, `enums`/`functions` as a ~1.2x box-load control floor): QTYPEIDX already removed the large majority of the terms behind `callable_deps` — attributable `field_dep` ~7.6x (36,901->4,055 ms), `sigtype` ~9.3x (13,192->1,188), `project` ~13x (12,819->820), `callable_deps` ~11.3x (28,978->2,143); **`declared_dep` barely moved (~1.6x, near the control floor)** and is now a top term largely by standing still. Residual defect found and fixed: `try_register_glob_reachable_symbol` (`lower_named_kind`'s MISS fallback, ~1.25M calls/stage-1 build per run12's 84% miss rate) had no early exit on failure and remembered nothing, re-sweeping O(glob targets x 6 linear surface name scans) per unbound-name occurrence, charged to `sigtype`/`project`/`field_dep`. Added a registry-pure-per-importer negative memo, a cached importer index, and routed the declares-item question through the existing NAMEIDX index | Phase 1 / §20 (HIR) | `hir_glob_reachable_sweep_unmemoized_2026-08-22.md`, `hir_glob_reachable_miss_memo_spec.spl`, perf-gate rows `GLBMEMO` |
| 2026-08-22 | hir / import resolution | `4f94fc7ff43` | **INVESTIGATION, no compiler change.** run13's HIR phase dies on `ambiguous explicit callable dependency \`Backend\` in \`compiler.backend.backend.env\`` (x2, same site, `llvm_backend.spl`). Not the duplicate-type-name class: `Backend` has exactly ONE declaration tree-wide (`backend_api.spl:166`, `type Backend = CompilerBackend`). Not a QTYPEIDX/GLBMEMO artifact either — `git log -S` puts the diagnostic in `4b88aebf00b`, before both. Root cause by source reading: `materialize_imported_callable_explicit_dependency_inner` runs a NAMED-import branch and a WILDCARD (glob) branch into the same `selected_target`, so a glob route can disagree with — and thereby VETO — an explicit named import, contradicting the method's own stated contract ("Glob/package inference is intentionally excluded here") and the explicit-over-glob precedent in `glob_ungate_swaps_import_winners_2026-08-01.md`. Fix designed (rank candidates; ambiguity only WITHIN a rank) but deliberately NOT landed: both harness fixtures pass pre-fix because the sweep is never entered for them (the dependency resolves at step 1, `register_imported_symbol`), and the instrumented single-module repro had not reached HIR lowering after ~1h on a 4-lane box. Shipped: bug record + contract-pinning spec | Phase 1 / §20 (HIR) | `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md`, `explicit_import_beats_glob_reexport_spec.spl` |
| 2026-08-22 | hir / import resolution (iter 2) | `980b83f05a9` | Follow-up on the `ambiguous explicit callable dependency \`Backend\`` lane. Instrumented `materialize_imported_callable_dependency` (env-gated `SIMPLE_AMBIGDBG=1`) and proved across four fixture shapes that the sweep carrying the defect is **never entered**: step 1 always binds, and not via the owner's own declarations but via the `else` "re-export facade chase" in `register_imported_symbol_inner` -> `find_reexport_source_walk`, which scans the SAME named AND wildcard import rows the sweep scans but is **first-match-wins with no ambiguity notion**. So the sweep is reachable only when that chase fails to BIND — via the `depth > 8` cap, the shared visited-memo (`seen_depth <= depth`), a `state.valid`/`complete` bailout, or the terminal `already_bound and not same_owner -> return` — while the sweep still finds 2+ candidates (it calls `find_reexport_source` per target with a FRESH state). A fifth fixture was discarded: it went red only on its own guard-the-guard (`explicit_dep_scan_count > 0`), i.e. green for the wrong reason. Real-tree trace still blocked on COST, not method: an interpreted single-module `compile` of `llvm_backend.spl` spent >4h still in the parser (6,919 lines, 0 traces) and was killed. Fix stays designed-not-landed | Phase 1 / §20 (HIR) | `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md` |
| 2026-08-22 | hir / import resolution (iter 3) | `ed4ca46f4c2` | Landed the AMBIGDBG investigation probe as a PERMANENT level-gated log (default OFF, `SIMPLE_AMBIGDBG=1`), per the log-retention policy rather than deleting it. Gate `hir_ambig_dep_trace_enabled` caches the env read once (`_hir_ambig_trace_state`, same shape as PROFOFF), so each of the ~20 sites costs one i64 compare when unset; every site tests the gate before building its message because interpolation happens at the call site. Covers the router and its three step guards, the facade chase outcome and all six of its bailouts (`depth-cap`, `visited-memo`, `route-arrays-misaligned`, `walk-state-misaligned`, `invalid-facade-index`, `export-origin-owner-unresolved`), the terminal `already-bound-other-owner` return, and the sweep (`sweep-enter`, per-candidate `route=named\|glob` with target+item, `sweep-verdict`). Default-off pinned by a new spec (2/2); verified live that `SIMPLE_AMBIGDBG=1` emits and unset is silent. Requested for run14 so the real `compiler.backend.backend.env dep=Backend` trace lands in the build log | Phase 1 / §20 (HIR) | `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md`, `ambig_dep_trace_default_off_spec.spl` |
| 2026-08-22 | hir / import resolution (iter 4, run14 trace) | `d06b3f5f880` (row CORRECTED in iter 5) | **RETRACTED CLAIM.** This row originally read "Symptom RESOLVED, defect LATENT — `ambiguous explicit callable dependency` zero times". That count was taken MID-PHASE (HIR 522/688) and was wrong: at 17:44Z run14 shows the diagnostic live at `llvm_backend.spl` (`source_idx=222`). Class E is **1** in run14 vs run13's terminal **2** — down, NOT closed. Lesson recorded: a count from an unfinished run is not a count; a zero measured before the phase ends is absence of evidence. The import-edge repairs `1aa81cac8c6` + `ead29e6df64` reduced the site 2 -> 1 (49 of 50 requests now hit `router-preresolved`); the remaining one enters the sweep and errors. The named/glob merge in the sweep is unchanged and demonstrably live: 630 `sweep-enter`, 9 `sweep-candidate`, **0 `ambiguous=true`** — every multi-candidate case agreed on its terminal. Fix stays unlanded: no input makes a spec red. **Resolution-path census (52,024 router calls): 27% preresolved, 4% bound by the facade chase, 69% fall through BOTH chase and sweep into the package-sibling fallback. `chase-bail` reasons: visited-memo 158,488 (97.1%), depth-cap 4,582 (2.8%), export-origin-owner-unresolved 129; the misaligned/invalid classes are 0.** So the chase declines because of the shared walk-state visited-memo, not the depth cap or corrupt surfaces — and the 69% fallthrough is a resolution-shape finding for the plan independent of this bug | Phase 1 / §20 (HIR) | `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md` |
| 2026-08-22 | hir / import resolution (iter 5) | `d06b3f5f880` | **FIXED: explicit-over-glob precedence, in BOTH the facade chase and the sweep.** run14 forwarded the build's single `sweep-verdict ambiguous=true` and it is this bug: `owner=compiler.backend.backend.env dep=Backend`, four candidate rows glob/glob/named/glob, the globs naming `compiler.frontend.parser_types_expr` (`enum Backend`) and the named row naming `compiler.backend.backend.backend_api` (`type Backend = CompilerBackend`) — **the glob won**, i.e. a wrong TYPE for `EvalContext.backend`, not just a noisy diagnostic. **Correction to iter 1: `Backend` is NOT unique tree-wide** — that census was scoped to `70.backend/`; there are 4 owned-code definitions, so this is a genuine two-owner collision of the `std.io` family (the run14 lane's discriminator, applied to my own claim). The trace also showed the defect is in TWO places: `find_reexport_source_walk` sets `matches = item_start == item_end` (a glob row matches ANY name) and scans rows in one ordered pass, so a glob in an earlier slot beat the explicit import and BOUND first — fixing only the sweep would have left the miscompile. Fix: chase does two passes (named rows, then globs; only the named pass scans item rows); sweep ranks candidates (`selected_rank` 1=named/0=glob, ambiguity computed only WITHIN a rank, two disagreeing EXPLICIT routes still report). Row-vs-pair check: the sweep does NOT miscount rows — it compares against the running selection, so arity was correctly 2; the real defects were precedence + last-writer-wins. Same trap IS live nearby and left filed-not-fixed: the bare-export sibling dedup compares only the LAST match (`sibling_match_index != sibling_index`), so A,B,A counts 3. Spec asserts the resolved OWNER (pins the miscompile, not the message): RED pre-fix, GREEN post-fix. Zero regressions — every neighbouring spec run on fix AND at baseline `d5e67ca1f60`, counts identical (`same_named_package_facade` 0/5 both sides, `resolve_import_symbols` 26/32 both, `reexport_physical_cache` 16/17 both, all pre-existing) | Phase 1 / §20 (HIR) | `ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md`, `explicit_import_wins_over_glob_owner_spec.spl` |
| 2026-08-22 | seed perf (interpreter) | `f593e9ce8dd` | ROOT defect behind the HIR codec cliff: a `me`-mutating method deep-cloned the field array whenever the receiver reached the mutating frame through >1 parameter hop, because every intermediate frame pinned a second Arc. The caller's binding is now parked across the nested call and restored from the callee's final value (the Bug #19 write-back already fixed that value), so all 384 accumulator classes passed as parameters go from O(n^2) to O(n). n=4,000 through 1 hop: 8,018,103 elements cloned -> 1. Genuinely live aliases still copy-on-write. | Phase 1 / §20 | `seed_receiver_multi_hop_cow_clone_2026-08-22.md`, `tests/interpreter_receiver_hop_depth_linear.rs`, perf-gate rows `HOPPARK` |
| 2026-08-22 | hir / guard coverage | `da90106fcd6` | run13 stage1 emitted `untyped function returns a value` x7 (all `src/lib/nogc_async_mut/array.spl`) while `check-untyped-return-value.shs` — added by `f9a7b5cb296` for this exact class, with `src/lib/*/array.spl` in its HARD scope — reported PASS. Two mirror holes: (A) `sig !~ /\) *->/` treated the `) ->` inside a function-TYPED PARAM (`predicate: fn(Any) -> bool`) as a declared return type, skipping every callback-taking untyped fn tree-wide (6 of 7 sites); (B) any typed-param ident counted as resolved, but the compiler resolves a param ident only through `hir_type_simple_name`, i.e. SCALARS only — `return arr` with `arr: [Any]` is ambiguous (`array_intersperse`). Closing both exposed a false positive, so the mirror also gained `declared_callable_type`'s untyped-param bail (`has_type_`), which removed 268 false entries from the ratchet baseline (410 -> 142, deletions only). 21 signatures typed across the three sibling `array.spl` files | Phase 1 / §20 (HIR, gates) | `untyped_return_guard_blind_to_callback_params_2026-08-22.md`, `untyped_return_callback_param_shapes_spec.spl` |
| 2026-08-22 | hir correctness / owner-side imports | `1aa81cac8c6` | run13 census class A/B root-caused. **The census's "bare type-name fragments" (`text` 5061, `i64` 2873, `bool` 2204, `Option` 1988, `f64` 819, `Any` 504) are NOT errors and NOT the non-injective-key bug of `5c38b388a53`** — the grep matched the *body* of the payload-origin ADVISORY ("a later `unresolved type: text` will be reported"). Anchoring to end-of-line collapses 15,014 hits to **338 real errors** across 14 names; 12,171 of the 12,364 advisory lines (98.4%) name a primitive. Three defects fixed: (A1) `parser_types_expr.spl` declares `ExprKind.CustomBlock(text, BlockValue)` but never imported BlockValue — its only import was `Span` — costing 47 errors + 193 advisories, and it was the ONLY non-primitive advisory in the run; (A2) `materialize_imported_callable_explicit_dependency_inner` ends its sweep with a bare `if selected_target < 0: return`, the same silent-return the PAYLOAD twin was fixed for on 2026-08-21 and never applied here, losing 12 type names (CodegenTarget 113, MirType 87, Export 26, TypeLayout 18, HirPattern 14, HirIfArm 11 …) with zero diagnostic naming the real owner — now an advisory, plus a lowercase-primitives-only `hir_dependency_is_builtin_type` filter (capitalized aliases and containers deliberately NOT filtered: `lower_named_kind` places their arms AFTER the symbol lookup so a declared `struct Bool`/`Result`/`Dict` wins); (B) `module_surface_declarations.spl` and `desugar/suspension_analysis.spl` reach parser_types_expr through a TWO-HOP PLAIN GLOB (neither hop is `export use`, so it does not transit), losing `parser_type_kind_named_name`/`parser_type_kind_array_element_name`/`expr_kind`/`stmt_kind` — fixed by explicit imports rather than widening either glob | Phase 1 / §20 (HIR) | `hir_unresolved_type_owner_missing_import_2026-08-22.md`, `enum_payload_owner_imports_dependency_spec.spl`, `dependency_builtin_type_filter_spec.spl`, `two_hop_glob_import_does_not_transit_spec.spl` |

| 2026-08-22 | hir correctness / owner-side imports (follow-up) | `214fdfac2db` | Follow-up to `1aa81cac8c6`, which fixed the DIAGNOSTIC gap and left the **291 real `unresolved type: X$` errors** it made addressable. Owner enumeration reproduces `materialize_imported_callable_explicit_dependency_inner`'s own predicate (declares / explicitly imports / one-hop glob-or-`export use` reachable, matching `find_reexport_source`). Two modelling errors had to be corrected first, both inflating the list: multi-line `use x.{\n a,\n b\n}` blocks ARE imports, and `TopLevelItem.Export` is a VARIANT access, not a type position. **49 explicit imports across 45 owner modules clear 273 of 291**: CodegenTarget 113 (2 owners), MirType 87 (36), Export 26 (1), TypeLayout 18 (1), HirIfArm 11 (1), CompilationContext 6 (1), AsmLocation 5 (3), AsmConstraintKind 5 (2), HirModule 2 (1), HirExpr 2 (1). Every edge already exists (60/70/90->50.mir, 35->30/20, 40->00.common, 20.hir->10.frontend, 70.backend->10.frontend per `hir_definitions.spl:22`) — no new cross-layer edge, no glob widened, no `export use` added, no diagnostic silenced. **NOT fixed and stated rather than papered over:** HirFunction (2) — its only candidate `20.hir/hir_types.spl:29` is provided by sibling `hir_definitions.spl`, which already does `use compiler.hir.hir_types.*`, so the import would be a CYCLE and the declaration must move instead; HirPattern (14) + CompiledModule (2) — no owner gap exists under the predicate (both are genuinely imported/re-exported), so those 16 are a different sub-shape needing the runtime `[hir-callable-dep-origin-unresolved]` line from a verification build | Phase 1 / §20 (HIR) | `hir_unresolved_type_owner_missing_import_2026-08-22.md` (Follow-up section); `callable_signature_owner_imports_dependency_spec.spl` — measured 4/4 FAIL pre-fix, 4/4 PASS post-fix |
| 2026-08-22 | hir perf / origin search | `22a0424891a` | **PAYLOADMISS.** run14 emitted ~31,700 in-flight `[hir-payload-origin-unresolved]` / `[hir-callable-dep-origin-unresolved]` advisories for BUILTIN CONTAINER spellings alone (`Dict` 14,847, `Option` 9,857, `Result` 7,015, `fn` 290), none of them a terminal error. Each one is a FULL failed origin search — owner declarations, then re-export routes, then the whole explicit import table — repeated per occurrence and per importer, for an answer that depends only on the frozen surface registry. **The naive capitalized-name filter is WRONG and was rejected:** `1aa81cac8c6` made `hir_dependency_is_builtin_type` lowercase-primitives-only on purpose, because `lower_named_kind` places the container arms AFTER the symbol lookup so a declared type wins, and 42 `Result` / 14 `Option` / 10 `Array` / 1 `Dict` declarations exist in-tree. Fix is a NEGATIVE memo `payload_origin_miss_memo` keyed `(owner, name)`: **only a MISS is cached**, so a declaration still resolves on step 1 of every search and precedence is untouched; sound because the resolve is a pure function of (owner surface, name) over the frozen `module_surfaces`, reading no symbol table and mutating nothing — the same invariance `explicit_dep_target_memo` already rests on. Owner-scoped, never global by name (two modules may spell the same name and only one declare it). The callable advisory dedupe uses a SEPARATE key namespace because its negative is narrower than the payload search's. Advisory now emitted once per (owner, name) instead of once per occurrence | Phase 1 / §20 (HIR) | `hir_builtin_container_origin_search_storm_2026-08-22.md`; `hir_payload_origin_miss_memo_spec.spl` 5/5 PASS (pre-fix: does not compile, the counter did not exist); `check-perf-regression-tests.shs` PAYLOADMISS rows, `PASS — 108 mechanism(s) checked, 0 regressed`. Measured before/after on two affected modules (concurrent runs, same seed): `50.mir/mir_lowering_types.spl` 1,484 -> **40** advisories (-97.3%), 207.4 s -> 160.4 s; `module_reexport_materialization.spl` 4,608 -> **70** (-98.5%), 914.9 s -> 932.0 s (wall noise on a contested box — the COUNT is the discriminating observable, not the wall) |
| 2026-08-22 | seed JIT / erased-receiver dispatch | `097fd8a8d3f`, `ef06897e050` | row RECONCILED from `doc/03_plan/.../critical_hardening_plan_2026-08-21.md` §27 (originally filed there by mistake; the fuller lane write-up stays in that file). A bare method on an `Any`/trait-typed receiver is dispatched at runtime over the receiver's vtable identity instead of bailing the whole module (`try_emit_vtable_type_switch`, `closures_structs.rs`); `struct Name(Trait):` now records a real `HirImpl` so such structs HAVE a vtable; two soundness bugs fixed on the way (by-value copy of a vtable-bearing struct dropped every field; a vtable slot on a selfless body read the receiver as its first argument). Stage1 `[CODEGEN-AMBIGUOUS-METHOD]` sites 18 -> 0, blocking bodies 6 -> 0 (`ef06897e050` declares `impl SmfReader for SmfReaderImpl`). Stage1 still de-JITs, on a different single cause (`rt_process_read_stdout_checked`) | §20 (JIT) | `jit_any_receiver_ambiguous_method_bails_stage1_2026-08-22.md`; `compiler/tests/any_receiver_vtable_dispatch_jit.rs`; perf-gate rows `ANYVTJIT` |
| 2026-08-22 | hir names (run13 follow-up) | `75a66d615bd` | cleared the remaining 18 run13 `unresolved name` occurrences deliberately left open by the earlier run13 row (std/builtin/type provenance) | Phase 1 / §20 (HIR) | `hir_unresolved_name_import_reachability_2026-08-22.md` |
| 2026-08-22 | compiler perf | `7541acc9f03` | import dirname computation made linear | Phase 1 | commit |
| 2026-08-22 | front-end parity | `6967d939916` | bodyless `if`: seed parser and pure-Simple front end diverge in BOTH directions (A: bodyless `if` + DEDENT -> seed ACCEPTS as a no-op, native parse-errors; C: bodyless `if` + same-column integer -> seed REJECTS, native ACCEPTS **and prints 2147483652 where 7 is correct** — a silent miscompile). Row B (flat body) agrees on both paths and is the seed's deliberate feature, not a divergence; control agrees, so the harness is non-vacuous. Seed mechanism located (`parse_block_after_newline` returns an empty Block on Dedent/Eof, an arm meant for `case nil:` match arms, shared with `parse_condition_block`); native half NOT root-caused yet, recorded as such. Tightening both is free: 0 sites across 15,190 owned .spl files. FILED not fixed — seed half needs a rebuild + match-arm regression pass, native half needs root-causing. | §20 (front end) | `doc/08_tracking/bug/seed_accepts_bodyless_if_native_build_rejects_2026-08-22.md`; fixtures `shapeA/shapeB/bodyless/control.spl` |
| 2026-08-22 | hir (MirType root cause) | `4a40c00c8e5`, `9f11967564b` | run14's 153 MirType `unresolved type` errors were NOT the owner-missing-import class the previous lane predicted (it forecast 402-459 cleared incl. MirType 87; run14 measured 486 vs run13's 479 — unchanged). Real owner, found via a new level-gated `[ist-proj-miss]` probe over a full stage-1 build, is `70.backend/backend/common/type_mapper.spl`, which imports MirType **explicitly on line 8**; the signature is `fn map_struct(fields: [(text, MirType)])` — an array-of-TUPLE. `imported_surface_type`'s array arm was keyed on `parser_type_kind_array_element_name`, which answers "" for BOTH "not an array" and "array of a non-Named element", so it fell to `lower_type` in the IMPORTER's scope. Same defect as the 2026-08-21 bare-tuple fix, one nesting level deeper. **General cause: the MATERIALIZATION walk (`parser_type_named_dependencies`, 11 constructors) and the PROJECTION walk (3) recurse over different TypeKind sets** — materialization binds the name correctly, projection never consults it, which is why ZERO `[hir-callable-dep-origin-unresolved]` ever fired for MirType across run14's 6.3M-line trace (codegen resolved MirType 76/76). Audited every constructor in the gap by probe, not by reasoning: `*T` and `A | B` were also LIVE (22 pointer params, 13 union positions in owned .spl) and are fixed too; `T?`/`@T`/`-T`/`[[T]]`/`[T?]`/`Dict<K,V>` measured 0 and were deliberately left alone. Rejected after measurement: an Optional/generic-arg fix (byte-identical pre/post, reverted). Recorded not fixed: `Weak` missing from BOTH walks; scalar branch drops generic args so `Dict<text,MirType>` loses fidelity silently. Two diagnostics kept (default off): `[ist-proj-miss]`, `[field-dep-unresolved]`. | §20 (HIR) | spec `test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl` — 4 examples, RED pre-fix at `d684064754b` (`unresolved type: MirType`), GREEN post-fix, bare-array control green both sides; `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (b)/(c). MEASURED full-build clearance (post19 vs run14, both reached `hir 688/688` and terminated rc=1 at the same point, both counted on the `[hir-fatal]` basis): **MirType 180 -> 0**, HirPattern 24 -> 0, HirExpr 6 -> 0, CompiledModule 3 -> 1; total unresolved-type **258 -> 48 (-81%)**, poisoned modules **56 -> 9 (-84%)**. HirModule went UP 6 -> 8 — recorded, not buried: previously-poisoned modules now lower far enough to REACH that check, so per-type totals are not a monotone progress metric. Survivors (AsmLocation 15, AsmConstraintKind 15, VhdlPortDirection 6, HirModule 8, HirFunction 3, CompiledModule 1) are the two OTHER mechanisms from follow-up (c) — generic callables returning `nil` before projection (`type_params.len() > 0`), and generic args dropped by the scalar branch — each needing its own lane. Measurement built the array-of-tuple fix only; pointer/union landed after and are not exercised by it. |
| 2026-08-22 | hir (generic-arg drop + walk parity guard) | `d481f15e1ac` | Closes both items follow-up (c) recorded rather than fixed. (c) blamed the PROJECTION alone for dropping generic arguments (`lower_named_kind(name, [], span)`); that is half the mechanism. `materialize_imported_callable_type_dependencies_inner` dispatches on the SAME scalar capture, so `parser_type_named_dependencies` — the walk that DOES recurse `Named` args — was reachable only from its `else` branch and **never ran for a generic**. The gap was SYMMETRIC, which is exactly why the `Dict<K, MirType>` probe read 0 errors and why (c) was right to warn that 0 must not be read as "handled". Consequence measured as a wrong OUTCOME, not a missing error: an imported `fn map_struct(d: Dict<text, MirType>)` was recorded in the importer's own symbol table as taking **`Dict<any,any>`** — key and cross-module value type both erased via `lower_named_kind`'s zero-arg `Dict` recovery arm, no diagnostic anywhere; post-fix `Dict<text,named>`. Sharper evidence: with the owner's `use` line stripped entirely the fixture still produced ZERO errors pre-fix. Fixed on both sides (`imported_surface_projected_named_args`; scalar-path materialization now also runs the full walk — a superset, idempotent, fast path preserved). `Weak` added to the materialization walk (latent: 0 `-T` type positions in owned .spl); projection side deliberately unchanged — HIR has no `Weak` kind and `lower_type` already erases `-T` to `Infer` without erroring — and that asymmetry is now RECORDED in the allowlist instead of silent. **The record's durable rule is now enforceable:** `scripts/check/check-type-walk-constructor-parity.shs` FAILs when materialization gains a constructor projection neither handles nor allowlists with a reason, and FAILs equally on a stale allowlist line; `PASS — 12 constructor(s) checked, 0 unprojected and unallowlisted`, `--selftest` fatal (4 fixtures), <5 constructors compared is ERROR not a pass. | §20 (HIR) | spec `test/01_unit/compiler/hir/imported_generic_argument_projection_spec.spl` — **2 of 4 FAIL pre-fix, 4/4 PASS post-fix** at `624ee9947f6`, asserts the recorded param type not merely the absence of an error, covers param + return paths, guard-the-guard strips the owner's import and must still fail; `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (d). Pre-existing red recorded not stepped over: `imported_tuple_signature_dependency_spec.spl` is 2/2 RED at origin/main with and without this lane's source changes. |
| 2026-08-22 | hir (generic callable projection) | `86787968989`, reverted by `ec13c319250`, RE-LANDED ALONE as `8f08930460d` | THIRD mechanism in the run14 `unresolved type` lane, distinct from owner-missing-import (`eeaf35d3be0`) and the array/pointer/union constructor asymmetry (`4a40c00c8e5`, `9f11967564b`). `declared_imported_surface_callable_type` opened with `if callable.type_params.len() > 0 ... return nil`, so a GENERIC callable's signature was never projected at all: the importer got a `SymbolKind.Function` symbol with a **nil type** — no parameter types, no return type, no projected identity for any cross-module type the signature names. Population is the generated fold visitors and codecs, where every walker is generic (`walk_ast_asm_location<C>(node: AsmLocation, ctx: C, f: fn(AstWalkNode, C) -> C) -> C`); their non-generic siblings in the same module projected fine. Fix projects them with the callable's OWN type params BOUND to `HirTypeKind.TypeParam` — the owner-scope lookup the old bail was dodging would have traded a dropped signature for a bogus `unresolved type: C` — plus a `Function` arm on `imported_surface_type` (same durable lesson as follow-up (c): `fn(A,B)->C` is in the MATERIALIZATION walk's constructor set, became reachable only once generic callables were projected, and without it this change would have emitted a fresh `unresolved type: AstWalkNode` on every generated-visitor importer). Monomorphization untouched (§9). **Negative result recorded, not buried:** the lane's lead predicted this bail also explained run14's AsmLocation 30 / AsmConstraintKind 30 / HirPattern 48 census names. Five measurements say it does not — synthetic generic callable, the real `f: fn(AstWalkNode, C) -> C` shape, an `export use` re-export hop with a live call site, a targeted lowering of the REAL `10.frontend/generated/ast_visitor.spl` under `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1` (every `[ist-proj-miss]` named a module absent from the probe closure; zero asm types), and a check that all six owner modules naming the asm types already import them explicitly. A nil signature type is SILENT by construction, which is why this mechanism never had a diagnostic and is why those census names are NOT claimed as cleared. | §20 (HIR) | spec `test/01_unit/compiler/hir/imported_generic_callable_signature_projection_spec.spl` — 4 examples, RED pre-fix (`expected -1 to equal 3`, i.e. nothing projected), GREEN post-fix, non-generic control green both sides, plus an assertion that type param `C` is never reported unresolved; `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (d). Pre-existing red at `624ee9947f6`, not this lane: `imported_tuple_signature_dependency_spec.spl` 2/2. **Reverted on SUSPICION (not evidence) by `ec13c319250`, which backed out this lane and the generic-ARGUMENT lane `d481f15e1ac` TOGETHER** because run15 regressed to 3716 fatals and no oracle short of a full stage-1 build could separate them. Re-landed ALONE (without `d481f15e1ac`) so run17 can measure it in isolation; verified not to drag the sibling in (`imported_surface_projected_named_args` and both call sites: 0 occurrences). Counter-evidence that it is not the run15 driver, agreed independently by the bisect lane (`a50b92999d2`): the largest new name HirContractBlock (472) appears in ZERO generic-callable signatures — its only cross-module use is the NON-generic `lean_backend.spl:528 fn function_contract_from_hir(name: text, contract: HirContractBlock?, param_aliases: [(text, text)]) -> Result<FunctionContract, CompileError>` — as do Span (111) and ModuleSurfaceExportOrigin (145); the victim `50.mir/hwir/bit_vector_constant.spl` has no `use` line at all and reports exactly the four `X?` optionals its facade importer names. Re-land condition agreed by both lanes: a measured stage-1 `[hir-fatal]` census at or below 48 fatals / 9 poisoned. See bug record Follow-up (g). |
| 2026-08-22 | hir (generic projection REVERT) | revert of `d481f15e1ac` + `86787968989` | **REGRESSION, REVERTED.** The two generic-projection lanes took full stage-1 `[hir-fatal]` from post19's **48 to 3716** and poisoned modules from **9 to 437**. Non-fatal recovered occurrences moved the OTHER way (234,210 -> 7,231), which is why a raw grep read as progress — recorded so the two are never conflated again; only the fatal count gates the build. Every new fatal name is a user type in a GENERIC-ARGUMENT position (`X?` == `Option<X>`, `Dict<K,X>`): HirContractBlock 501, SymbolId 444, MirFunction 171, ModuleSurfaceExportOrigin 159, HirType 144, Span 141, LayoutPhase 84. `Option`/`Result`/`Dict` themselves are NOT fatal — they resolve, their arguments do not. Mechanism is THIS lane's own owner-missing-import defect reached from a new direction: the recursed argument is looked up with `lookup_qualified_type_raw(imported_module_name, name)` where `imported_module_name` is the module the importer NAMED — a package facade / glob re-exporter — not the module that DECLARES the type; on the miss `imported_surface_type` falls to `lower_type` in the IMPORTER's scope and hard-errors against a module that never names it. Victim `50.mir/hwir/bit_vector_constant.spl` has **no `use` line at all** and reports exactly the four `X?` fields `50.mir/mir_instruction_graph.spl` imports at lines 3-5; its profile reads `qtype=4725/3781 miss` (80%). Widening projection did not create the gap, it made an existing one fatal at scale. Reverted rather than fixed forward because the correct fix (owner-scope resolution following the re-export hop to the declaring module) has no oracle short of a ~5 h stage-1 build, and 437 poisoned modules must not sit on main. `4a40c00c8e5` / `9f11967564b` / `22a0424891a` KEPT — measured net wins. **Honest limits recorded, not buried:** no unit fixture reproduces it (the new spec is green on BOTH sides and says so in its own docstring); per-commit attribution is STATIC (diffs + failing-name shape), not a differential build — two targeted `--entry-closure` probes never reached the HIR phase for the victim (rc=1 in 178 s, 0 fatals). | §20 (HIR) | `doc/08_tracking/bug/hir_generic_projection_regression_run15_2026-08-22.md`; `hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (e); guard spec `test/01_unit/compiler/hir/imported_optional_argument_reexport_hop_regression_spec.spl` (3/3 green both sides, labelled NOT a reproducer). Pre-existing red stepped over and recorded: `imported_surface_callable_projection_spec.spl` 2 of 3 RED at pristine `c05e7052843` and byte-identical after the revert. |
| 2026-08-22 | hir (provider-gap type imports) | `49d764f48ae` | FOURTH mechanism in the run14/run16 `unresolved type` lane, and the only one that is not a projection defect: `use <provider>.{TypeName}` where `<provider>` neither DECLARES nor re-exports `TypeName`, so nothing is projected, the annotation falls to `lower_type` in the IMPORTER's scope and hard-errors. Type-position sibling of the already-fixed `unresolved name` import-reachability class. Three of run16's 15 distinct fatals: `VhdlPortDirection` (`70.backend/backend/vhdl_type_mapper.spl` had NO import at all, relying on `compiler.mir.mir_data.*`; declared in `50.mir/mir_instruction_support.spl:104`), `HirFunction` (`vhdl/vhdl_design_catalog.spl` named `compiler.hir.hir_types`, which exports `HirModule` but nowhere declares or exports `HirFunction`; real owner `20.hir/hir_definitions.spl:35`), `CompiledModule` (`80.driver/driver_pipeline_execution.spl` named `compiler.backend.codegen`, which declares `CodegenPipeline` at line 673 and no `CompiledModule` at all — one `use` line carrying one symbol that resolves and one that cannot; real owner `70.backend/backend/backend_types.spl:333`). Fixed by importing from the DECLARING module — no resolver change, no facade hop, so the run15 flood shape is impossible by construction. **The compiler already prints the oracle for this whole class unprompted** (`[use-warning] '<Name>' is named in \`use <provider>.{...}\` but module '<file>' does not provide it`), so no full stage-1 build is needed to find or verify a member. The anticipated `HirFunction` cycle does not exist: `vhdl_design_catalog.spl` is a backend module, so the `hir_definitions` import adds no new edge into `20.hir`. **`HirModule` NOT cleared and recorded as a different shape:** `mono/instantiation.spl` (the file run16's fatal names) contains the string `HirModule` nowhere, nor does anything it imports, and a tree-wide sweep finds all 13 `use` sites taking it from `hir_types`, which does declare and export it — so there is no provider gap; open hypothesis (untested) is a MISREPORTED name, `HirModule` being the index-0 declaration of `hir_types.spl`. | §20 (HIR) | spec `test/01_unit/compiler/hir/hir_unresolved_type_import_provider_spec.spl` — **1 of 4 passed / 3 failed pre-fix at `340d54e97bb`, 4/4 post-fix**, incl. a controlled comparison asserting the named providers do NOT declare the types. Isolated `native-build` under `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1`, pristine vs fixed: `vhdl_type_mapper.spl` `unresolved type: VhdlPortDirection` x2 -> **0 `[hir-fatal]`**; `vhdl_design_catalog.spl` `unresolved type: HirFunction` -> **0**. Stated not papered over: `driver_pipeline_execution.spl` does not reach its fatal in a single-file closure (0 both sides); its gap is proven statically. `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (h) |
| 2026-08-23 | front-end divergence / parser | `544b1b73411` | **BODYLESSIF.** A bodyless `if cond:` diverged between the two front ends in BOTH directions, and one cell silently MISCOMPILED. Pure-Simple `parse_block()` had no statement-start gate on its flat-body path, so `if flag:` + same-column `7` swallowed the 7 as the body; `probe()` then had no tail expression, its `-> i64` return slot was never written, and the caller printed the stale register value `2147483652` (`0x80000004`) instead of 7 — a well-formed AST all the way down, which is why nothing downstream complained. Seed side: `parse_block_after_newline`'s empty-block arm (documented as existing for `case nil:`) leaked into `parse_condition_block`, so a bodyless `if` before a Dedent was accepted as a no-op. Both now reject; `pass` remains the way to write a deliberate no-op and the flat-body feature (same-column `if`) still works. Correction to the record's proposed fix: match-arm bodies reach the empty arm via `parse_inline_or_block` -> `parse_condition_block`, NOT `parse_block`, so the gate is `parse_condition_block_allowing_empty` (7 conditional sites pass false, `parse_inline_or_block` passes true). Blast radius verified by measurement, not text scan (a naive column heuristic returns 1,702 false hits from wrapped signatures): `-p simple-parser` green apart from one pre-existing unrelated failure, and a multi-module `native-build` on the rebuilt seed reached MIR lowering with 0 `parser_error` lines | Phase 1 | `seed_accepts_bodyless_if_native_build_rejects_2026-08-22.md`; `scripts/check/check-bodyless-block-parity.shs` (PASS — 8 cases, 0 divergent); `parser/tests/bodyless_condition_block_gate.rs` (6 tests) |
| 2026-08-23 | hir (asm owner import inside a docstring) | `91fe715e556` | 12 of run16's 15 stage1 `[hir-fatal]` occurrences (8 of 14 file x type pairs): AsmConstraintKind 6, AsmLocation 6. **A FIFTH mechanism, and the cheapest so far — no resolver change.** `70.backend/backend/_CBackendTranslate/class_core.spl` carried `use compiler.frontend.parser_types_expr.{AsmConstraintKind}` / `{AsmLocation}` at lines **371-372, inside a triple-quoted docstring body** attached to the `bulk_copy` arm. They are string CONTENT, never `use` statements: the module surface bound neither name and `asm_constraint_for_c(kind: AsmConstraintKind, location: AsmLocation)` had two unbindable signature dependencies. `instruction_lowering.spl` is plain class A — names AsmConstraintKind in four match arms, imports it nowhere. **Two competing hypotheses measured and both NEGATIVE, recorded not buried:** run16's log contains **zero** `[use-warning]` lines naming either type, so `49d764f48ae`'s provider-does-not-provide oracle is silent here (a statement that does not exist cannot warn about its provider) — which is exactly why this needed its own lane; and `10.frontend/parser_types_expr.spl:803,809` really does declare both enums, so the named provider was correct all along. The `type_params > 0` bail stayed rejected. The single `[hir-callable-dep-origin-unresolved]` line in run16 naming either type named this one owner, and the four modules that hard-errored (`c_backend_translate`, `c_codegen_adapter`, `export_wrappers`, `instruction_lowering`) import `MirToC` — the innocent-third-party blame this record opened with, one owner accounting for all 8 pairs. **Durable lesson: a whole-file grep for an import is not evidence the import exists** — `class_core.spl` would have passed such a check for months, so import checks must be header-scoped. | §20 (HIR) | spec `test/01_unit/compiler/hir/asm_owner_import_inside_docstring_spec.spl` — 2 examples, **2/2 RED pre-fix, 2/2 GREEN post-fix** on the deployed seed, header-scoped import predicate plus a `names_type` guard-the-guard per example so the pin cannot pass vacuously; `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (i). Landed as a source fix, so the run15 generic-projection flood shape is impossible by construction. NOT claimed: the facade-hop owner-scope resolution defect of follow-up (e) is untouched and still open; full-build clearance is left to the next stage1 run rather than asserted here. |
| 2026-08-23 | hir (signature-type import provenance) | `84a5bdb5df6` | FIFTH mechanism in the `unresolved type` lane. `HirModule` was attributed to `mono/instantiation.spl`, a file that does not contain the string `HirModule` at all. Root-caused by MEASUREMENT at the single fatal emit site (`20.hir/hir_lowering/types.spl:957`), whose landed probe prints the span: **`span_file=` is EMPTY and `span_line=0`** — positive proof the type node was never parsed from any source and was rebuilt by the imported-surface projection. That also **refutes** the previously-recorded index-0 misreported-name hypothesis: `name` at that site is the same string the failed lookup used, so `HirModule` genuinely is the name being resolved, and the `5c38b388a53` id-0 family does not apply. Reproduced in **~40 min, not the 72-min full build**, with `--entry-closure --entry 40.mono/__init__.spl`. Defect class: an owner names a cross-module type in SIGNATURE position while reaching it only through `use X.*`; the projection accepts only a declaration, a re-export hop, or an explicit import as an ORIGIN, so the projected surface carries none and the IMPORTER hard-errors. **Both existing oracles are silent BY CONSTRUCTION** — `[use-warning]` reports a brace-list import whose provider lacks the symbol, and here there is no import statement at all; `[hir-callable-dep-origin-unresolved]` emits 0 lines for the name, the same silence recorded for MirType in follow-up (b). Population fixed, not just the instance: a header-scoped sweep found **29** owners of `HirModule`/`CompiledModule` in this shape (latent fatals that surface as importers lower further — the same effect that took HirModule 6 -> 8 in post19), all now importing from the declaring module. **NEGATIVE RESULT recorded, not buried: the two `HirModule` fatals SURVIVE the fix** — the glob gap in `monomorphize_integration.spl` is a real instance of the class but is not their cause, so `HirModule` stays OPEN with the span evidence as the durable finding; next step is a probe at the projection site printing the OWNER being projected, not another static sweep. `CompiledModule` is likewise REOPENED: the Asm lane's run18 measured that the `backend_types` import did not clear `driver_pipeline_execution`. | §20 (HIR) | ratchet `scripts/check/check-signature-type-import-provenance.shs` — `PASS — 1809 file(s) checked, 0 offender(s)` in **5s** on the fixed tree, `FAIL — 1809 file(s) checked, 29 offender(s)` on pristine (proven to discriminate); `--selftest` fatal, 8 fixtures encoding BOTH directions of the shared durable lesson that **a whole-file grep for an import is not evidence the import exists** — must-FAIL: glob-only, import-shaped line inside a **docstring** (the Asm lane's shape), commented-out import; must-PASS: real single-line import, real **multi-line brace-list** continuation (the false positive this lane's own first sweep produced), type named only in a comment; plus empty-tree and empty-table non-vacuity. Spec `test/01_unit/compiler/hir/hir_unresolved_type_import_provider_spec.spl` **3/7 pre-fix -> 7/7 post-fix** with a fixture-based guard-the-guard. `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (i) |
| 2026-08-23 | hir (importer-side generic-argument binding + auto ratchet) | `5aa2e2f5034`, `591d65b5e8e`, `308d222dc23` | **`HirModule` root-caused and `mono/instantiation.spl` CLEARED**, by two new level-gated owner probes at the `imported_surface_type` fall-throughs (`[ist-scalar-fallthrough]`, `[ist-catchall-fallthrough]`) — `[ist-proj-miss]` covers only `imported_surface_type_projected`, which is exactly why this name produced zero probe lines of any kind. The probe says `name=Dict owner=compiler.mono.monomorphize_integration lowering=src/compiler/mono/instantiation.spl`: the owner hypothesis was right, but the name that falls through is the **OUTER generic** of `Dict<text, HirModule>`. The whole type is then handed to `lower_type` in the IMPORTER's scope, which recurses into the generic ARGUMENT there — so **what the owner imports is irrelevant once that happens**, which is why follow-up (i)'s owner-side import could not have helped. Measured, and it is the load-bearing negative result of this lane: an owner-side batch of **75 imports across all of `40.mono` left the fatal count COMPLETELY UNCHANGED**, while a single IMPORTER-side `use compiler.hir.hir_types.{HirModule}` took `instantiation.spl` from 8 `unresolved type: HirModule` occurrences to **0**. Consequence stated plainly: the tree-wide sweep is owner-side BY CONSTRUCTION (it finds modules that NAME a type without importing it) and can never find this defect, because the importer does not name the type at all — the sweep removes LATENT origin gaps (prophylactic; it stops future fatals surfacing as importers lower further, the effect measured when clearing `CompiledModule` revealed 10 new `LocalId` fatals in `backend_types.spl`), and only an importer-side binding clears an ACTIVE fatal. Batching-then-measuring is what caught this; landing the full 1,657-row sweep as "the fix" would have been a false claim. `LocalId` (44 owners) landed as the same prophylactic class. Still open: the barrel `40.mono/__init__.spl` (4 occurrences), under test with the import placed before its `export use` lines. | §20 (HIR) | ratchet `scripts/check/check-signature-type-import-provenance.shs --auto` derives the type -> declaring-module table FROM THE TREE (every top-level `struct`/`class`/`enum`/`trait` under `src/`) and drops multi-declaration names into an ambiguous report for human judgement rather than guessing: **`files 14454  types 13522  ambiguous EXCLUDED 1822  FAIL 2620 offender(s)` in 19s**, cross-validated to the exact same 2620/1822 by an independent Python implementation. ADVISORY (honestly RED at 2620); the curated-row mode stays `PASS — 1810 file(s) checked, 0 offender(s)` and is what is safe to enforce today. Auto selftest fatal, 5 further fixtures (unique type must flag; AMBIGUOUS two-module name must be excluded not guessed; excluded builtin must not flag; type-parameter-shaped name must not flag; ambiguous name must reach the report). Exclusions are data with reasons (`struct Bool` really exists in `src/lib/*/ndarray`, so an import could SHADOW the primitive). Implementation note kept: the scan is a SINGLE awk process reading the file list itself — a first version piped through `xargs`, which splits on `ARG_MAX`, so each split built its OWN declaration map and returned a plausible-looking wrong answer (2538 vs 2620). `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md` Follow-up (k) |
| 2026-08-23 | build parallelism / worker memory | (this change) | **PARSE-SHARD SLIM ENTRY WAS SILENTLY REVERTED.** `6cedd51faec` (orphaned-claim reclaim) rewrote `run_parse_shards` from a stale base and put `native_build_worker.spl` back where `5409b246adc` had installed the slim `parse_shard_main.spl` — a stale-snapshot clobber; its commit message never mentions the entry, and the reclaim work it added is entirely orchestrator-side, so the two are orthogonal. Cost: every parse-shard child loaded the whole compiler closure (665 modules / ~3.3 GB) to parse ~80 files instead of the parse lane (383 modules / 0.88 GB) — 3.82 vs 1.54 GB per shard, ~18 GB of avoidable RSS per `--threads 8` run, which is why three concurrent runs saturate a 125 GB box. `test/01_unit/compiler/driver/parse_shard_slim_entry_spec.spl:16` asserts exactly this and has been RED on main since; `check-parse-shard-rss-budget.shs:21` derives its entry from whatever the source names, so it budgeted the wrong binary rather than failing; `check-perf-regression-tests.shs` has no row. Fixed by restoring the one line (semantics-preserving: sharding is a cache warm-up that cannot change output). Measured live, read-only, over 41 running workers / 521 samples: RSS 2.40->2.74 GB monotone and never released, `VmPeak` 3.37 GB, **99.4% anonymous**, one `[anon:mimalloc]` mapping of 2450 MB, `Pss ~= Rss` with only 14 MB shared — i.e. N workers cost N x full private heap, nothing is shared. Also found: thread count is derived from CPU only (`bootstrap-from-scratch.sh:897-945`, `host_cpus/2` = **16** here) with **no memory-pressure backoff anywhere** (`check-heavy-work-preflight.shs` is a one-shot admission gate, not a feedback loop); a memory-aware clamp and a ranked duplication list are proposed, not implemented. Report: `doc/09_report/build_parallelism_memory_audit_2026-08-23.md`. Bug: `doc/08_tracking/bug/parse_shard_slim_entry_reverted_6cedd51faec_2026-08-23.md`. Follow-ups (a) perf-regression row pinning the slim entry (b) `run_hir_shards` has no slim entry (c) the RSS budget guard should assert its entry. |
| 2026-08-23 | build harness / process wait | `ce3c2bf6c71` | **Shared crash class costing every affected stage1 run a full ~70min attempt** — run18 attempt 1 (rc=255 at `hir 181/688`, wall 4107s), run17 attempt 1 (rc=255, 3811s) and two `--entry-closure` probe runs, all printing `native-build worker wrapper exited abnormally (signal or wait failure, code -1) ... its process group has been terminated`. **Not** OOM, not disk-full, not the resource monitor, and not the one self-reported over-broad `pkill` (timestamps clear run18) — those were excluded by measurement first. Root cause is three composing defects, class **(b) a healthy child's status is lost**, not (a) or (c): `rt_process_wait()` in `runtime_process.c` did `if (waitpid(..., WNOHANG) < 0) return -1;` with **no EINTR retry**, so any signal delivered to the WRAPPER over a multi-thousand-second build read as a failed wait (the Rust `env_process.rs` twin had the same hole via `ErrorKind::Interrupted`, plus a poisoned `SPAWNED_CHILDREN` mutex turned into a permanent -1); **both runtimes collapsed every non-exited status onto the same -1** as the error path, which is precisely why the message has to hedge "signal or wait failure"; and `process_run_timeout_live`'s poll loop left on any non-`-2`, so that spurious -1 escaped with a LIVE worker and the unconditional `if exit_code != 0: _process_kill_group(pgid_file)` `pkill -KILL -s`'d the whole session — a recoverable hiccup converted into a lost hour. Fix: retry EINTR in both runtimes; report `128+signo` for a signal death so -1 means *only* indeterminate; keep the child tracked on an indeterminate error; new `_process_group_alive()` (`pkill -0 -s`, the same session id the kill path uses) so an indeterminate -1 over a live session keeps polling and never reaps the group; wrapper message now states the status was lost and the group was **left intact**. Rust half needs a seed rebuild; C + Simple halves are live immediately. | Phase 1 | `src/runtime/test/rt_process_wait_eintr_selfcheck.c` executes the REAL `rt_process_wait` against a real child under an `ITIMER_REAL` handler installed **without** `SA_RESTART` — **pre-fix `got -1, want 7`** (byte-for-byte the production `code -1`) and `got -1, want 137`; post-fix 4/4 green. Gate `scripts/check/check-process-wait-eintr-retry.shs` = `PASS — 3 check(s) executed, 0 failures`, `--selftest`-equivalent builds a deliberately de-fixed runtime copy and requires it to FAIL. `doc/08_tracking/bug/native_build_wrapper_wait_eintr_misreported_as_abnormal_2026-08-23.md` |
| 2026-08-23 | runtime perf | `(this commit)` | C-runtime dict resized by doubling only, so `d[k]=v; d.remove(k)` grew the table on tombstones alone — 34.9 MB for a dict with 0 live entries; same-capacity rehash guard added, footprint flat over a 64x churn range | §20 (runtime) | `c_runtime_dict_tombstone_churn_unbounded_growth_2026-08-23.md` |
| 2026-08-23 | build cache / HIR closure key | `5b4dda5bc21` | **HIR closure cache re-key BLOCKED on a correctness gap — the 0% hit rate is left in place deliberately.** `hir_cache_closure_digest` (`80.driver/driver_hir_cache.spl:84`) folds every surface's raw file `content_hash`, so one comment or body edit anywhere in the closure invalidates **all 687 entries**: the incremental hit rate is **0% by construction** on a ~60min phase, and the cache pays only for byte-identical repeat builds (`doc/09_report/cache_effectiveness_audit_2026-08-23.md`, `de7c994627e`). The proposed re-key onto `interface_digest_of_source` is safe only if that digest is COMPLETE — an under-capture is a stale cache **HIT**, i.e. a silently wrong compiler binary, whereas an over-capture merely over-invalidates. Differential spec written FIRST, one interface-only edit and one paired body/comment-only edit per construct: **RED at 6 of 12** pre-fix. Closed: `extend` headers (a retarget with byte-identical method lines was invisible) and `use` lines (a re-export alias `use m.{a as b}` + `export b` changed the exported symbol invisibly; capturing every import over-invalidates, the safe direction). Already covered and verified: `impl` blocks and trait default methods (signature-sensitive, default-body-insensitive). **NOT closed, and therefore the re-key was NOT applied: struct/class FIELD lines.** Field layout is directly downstream-visible; a line-prefix extractor cannot separate fields from body statements, match arms, dict literals or named arguments without over-capturing to the point the digest approaches the content hash — and that still would not be a *proof* of completeness against the grammar. Unblock path is the semantic `35.semantics/interface/compile_interface.spl` digest, which already encodes `FieldSignature` but is compute-and-log only and needs typed HIR rather than raw source (it also still lacks generic arity+constraints, effects, passing modes, public constants). **No hit-rate change is claimed** — nothing was re-keyed, so there is nothing to measure; the deliverable is the completeness verdict. Out of scope and unchanged: `dep_iface_gate_*`, `needs_recompile` and `smf_manifest_entry_verifies` still have zero external callers and nothing traverses `simple.sdn` `dependencies:`, so no dependency-aware rebuild exists — not worth wiring until the digest is complete. | §20 (build cache) | spec `test/01_unit/compiler/driver/interface_digest_differential_spec.spl` — **6/12 RED pre-fix, 12/12 GREEN post-fix**, with the two struct-field cases asserting the gap AS IT IS (`does not change the digest ...`) so it cannot be silently laundered by a future re-key. `interface_digest_wiring_spec.spl` 12/12 and both `persistent_code_cache*` specs green (21/21) after the extractor change. Perf-gate rows `interface digest captures extend headers` / `... use/re-export aliases` / `HIR closure digest still keyed on content_hash` (`PASS — 113 mechanism(s) checked, 0 regressed`). `doc/08_tracking/bug/hir_closure_digest_rekey_blocked_by_incomplete_interface_digest_2026-08-23.md` |
| 2026-08-23 | driver / observability (step 3) | `0c085525541` | **step 3/6 could fail with rc=255 and ZERO output.** `src/app/lint` (140-module closure) printed `hir 140/140 step 2/6` and then exited 255 with no `error:`, no `[mono]` receipt, no step-3 line. Two gaps, same class: (a) NOTHING between the per-module HIR loop and `mir step 4/6` emitted `log_build_progress` — post-HIR finalize, value-struct-layout validation, typecheck/safety/any-escape/enum-contract passes, AST reset, all of monomorphization and `post_mono_verify`; `log_phase` covers some but is env-gated OFF by default. (b) the phase-3 error preview was gated on `SIMPLE_BOOTSTRAP_DEBUG=1`, so the default config printed a bare `phase 3 FAILED` — the identical defect already fixed for phase 2 a few lines above and never swept to 3/4. Swept the class: start+terminal receipts for `hir_finalize`, `post_hir_validate`, `hir_reclaim`, `typecheck`, `safety`, `any_escape`, `enum_contract`, `monomorphize`, `post_mono_verify`, `borrow_check`, `process_async`, `optimize_mir`, `weave_aop`, terminal `mir`, plus the three step-5/6 failure returns in `driver_aot_native_output.spl` that returned without any `terminal=failed` receipt (module-outcome refusal, zero object files, link `Err`). New coded diagnostics `E-DRV-PHASE3-000` / `E-DRV-PHASE4-000` (failing verdict with ZERO recorded errors = internal invariant break, said out loud) and `E-DRV-MONO-001` (mono refused because phase 3 did not admit). | §27 (observability) | `step3_silent_rc255_no_phase_receipt_2026-08-23.md`; `test/01_unit/compiler/driver/step3_phase_receipt_contract_spec.spl` (5/5) |
| 2026-08-23 | perf (interpreted lint char walk) | `78b4197d649`, guard `8b87dc23b13` | **CHARWALK.** The SIGPROF sampler's two largest interpreted-lint self-time frames — `count_triple_quotes` 5.8% and `raw_rt_lexical_code_lines` 5.5% — were not proportional to anything the lint has to know. Both paid full per-character interpreted cost on characters no branch of the scanner can act on: the blanking scanner took a 1-char `substring` PLUS an **unconditional** 3-char `substring` (a `"""` can only start at a `"`) plus one `pieces.push` per character, so a 60-char line cost ~120 interpreted allocations and 60 array pushes to reproduce itself byte-for-byte; `count_triple_quotes` took a 3-char `slice` per character of lines holding no `"""` at all. **A prior lane looked at exactly these two frames and stopped, recording them as "proportional to work — not interpreter bugs". That premise is the durable lesson: proportional to CHARACTERS is not proportional to WORK.** Fixed by run-based scanning with the state machine untouched — reject a line with no `"""`; copy ordinary text to the next `"`-or-`#` in one slice; blank comment tails and triple-quoted spans with one `repeat`; probe for `"""` only at a quote; hoist the length. **Concurrency recorded rather than smoothed over: a parallel lane landed the whole-line skip (`clean_line` returns `raw_line` when the line holds neither `"` nor `#`) mid-flight and refactored the function into `RawRtLexState`.** That work is kept as upstream wrote it and this lane re-based onto it and RE-MEASURED, so the headline number is the marginal one. Correctness was the gate: **byte-identical output on 150 real `src/**/*.spl` files** (57,385 emitted lines, `diff` clean), on an adversarial fixture set (`#` inside a string, quote inside a comment, escaped quote, `""""`, unterminated string carrying state across a line boundary, multi-line triple blocks), and on `simple lint` end to end. `ARR_MUT_CALLS` (`SIMPLE_PERF_COUNTERS=1`) **740,481 -> 218,684 (3.4x)** against current upstream; **1,267,276 -> 218,684 (5.8x)** against the base carrying neither fix. Wall 28.89s -> 12.04s, corroboration only — this box moves 2x between runs of identical code. **Scope stated, not implied: the lexer half of the lane (`char_slice`/`char_code`/`char_code_inline`/`advance`, 4.8+4.6+2.4+1.7%) is untouched and still open.** | §20 (perf) | `doc/08_tracking/bug/lint_per_char_lexical_walk_2026-08-23.md`; spec `test/05_perf/lint/lint_lexical_char_walk_perf_spec.spl` — **2 of 4 RED pre-fix / 4/4 GREEN post-fix** on the CURRENT base: long-run-vs-choppy ratio 1.13 -> 15.5 and docstring-scan ratio 1.26 -> 10.5, with a guard-the-guard asserting both sides are the same length AND both carry a quote so the earlier whole-line skip cannot satisfy the pin; the other 2 examples assert byte-identity against an inlined copy of the pre-fix walk and pass in BOTH directions by design. 8 `CHARWALK` mechanism rows in `scripts/check/check-perf-regression-tests.shs`, landed in their own commit per the §27 process rule. **Unrelated red observed and NOT touched: `check-perf-regression-tests.shs` lost 35 `must_*` rows between `01507771ec8` (110) and current origin (75) — a clobber by another lane, outside this range; this push is a strict superset of origin and removes nothing.** |
| 2026-08-23 | hir generic projection | `350dd6bff2b` (spec `9f2719af402`) | follow-up (e) FIXED: materialization never walked generic ARGUMENTS on the scalar-head path, so projection had no scope to resolve them in — this is why `d481f15e1ac` flooded stage-1 50x. Four guarded sites (composite-FIELD + callable param/return materialization; `imported_surface_type` head-and-args; `imported_surface_type_projected` delegation), class swept by enumerating every occurrence of the dispatch idiom. Spec lands SEPARATELY so a revert of the fix cannot delete its own reproducer | §20 (HIR completeness), §27 | `imported_generic_head_argument_owner_scope_spec.spl` 8/9 RED without fix, 9/9 with, measured on the landing base; 11-spec imported-surface family A/B byte-identical (0 newly red/green); `check-type-walk-constructor-parity.shs` PASS 11/0; 428-module closure A/B fatals 0 vs 0. FULL stage-1 census NOT obtained — origin/main dies at step 0/6, see record |
| 2026-08-23 | tests / in-development tag | `ebca59fe284` | **DATA lane: 1 spec tagged, not a backlog.** Surveyed 19 specs by targeted re-run (all of `test/01_unit/compiler/mono/`, `semantics/union_narrowing_spec.spl`, `driver/mono_pipeline_surfaces_unresolved_generic_spec.spl`): **18 GREEN, 1 RED**. Three of the named in-development candidates are simply PASSING today — impl-method templates 5/5, union narrowing 10/10, mono pipeline 2/2 — so tagging them would have marked green tests expected-to-fail. Two more (generic struct *instantiation* rewriting / f01 `unresolved method call: to_text`; the 33 unlowered `MirInstKind` variants) are genuine unfinished work with **no red spec to tag** and are left untagged. Only `free_generic_fn_two_module_native_spec.spl` (0/4) qualified: born RED with its own feature commit `625c245bafa`, never green, so unfinished #158 Phase B/C — not a regression. Tag carries site `40.mono/monomorphize_integration.spl:1079` + an explicit unblock condition per `.claude/rules/testing.md`. **Separately: the recorded test DB is unusable as a failing set** — `test_result.md` reports Passed 0 / Failed 0 over 770, `test_db.sdn` holds 74 counter rows for 770 tests and its `tests->suites->files` join yields mismatched rows; the failing set outside the surveyed dirs is therefore UNKNOWN and is stated as such. Tag is inert until the core lane lands `@tag:` in the pure-Simple runner | §27 (tests) | `doc/09_report/in_development_test_inventory_2026-08-23.md` |
| 2026-08-23 | seed interpreter / module loader (tooling latency) | (this change) | **PROBEMEMO.** The two import-resolution probes in `interpreter_module/module_loader.rs` (`sibling_might_define_requested_names`, `file_plausibly_provides_names`) did a full `fs::read_to_string` plus a substring scan or whole-file identifier tokenize on EVERY visit, uncached across call sites; the loader deduplicated only within a single directory scan, and that scan re-runs once per importing module. Measured by `strace` on a lint of a TWO-LINE file: **3,819 successful `.spl` `openat`, zero ENOENT, over 423 distinct files — `10.frontend/core/ast.spl` 866 times, `core/tokens.spl` 848 — 67.7 MB read for 5.1 MB of distinct content, 13.3x amplification**. `O(importers x siblings x filesize)`, driven by the COMPILER's own import graph rather than by the file being processed, which is why a trivial fixture and a 1,901-line one cost nearly the same, and why it taxes `test` and `run` as much as `lint`. Fixed with `module_cache::probe_source_cached()`, a per-PROCESS content memo (`None` = over the size cap or unreadable — the same classification the probes previously recomputed), cleared by `clear_module_cache()`. Deliberately NOT an on-disk cache: the `edit src/lib, no build needed` property in `.claude/rules/commands.md` is load-bearing and stays intact. **Two findings recorded rather than buried.** (1) The superlinear lint term this lane was briefed to hunt **no longer exists**: `50.mir/hwir/zca_rows.spl`, documented as `>2400s (killed), exceeds any practical budget`, now lints CLEAN in **44.3s** (>54x), and prefixes of 2/48/293/633/1,170/1,901 lines cost 37.9/36.4/39.2/39.1/37.0/44.3s — flat. The old cost table misrouted this lane and is corrected. (2) **`SIMPLE_INTERP_SAMPLE=1` and `SIMPLE_LOADER_TRACE=1` emit NOTHING from the deployed seed** on 37-44s runs; the binary predates them, and attach profiling is blocked here (`ptrace_scope=1`, `perf_event_paranoid=4`). All evidence above is from `strace`, which needs no cooperation from the binary. A seed redeploy is a prerequisite for the documented in-process route. | §20 (seed interpreter) | reproduce test `compiler/tests/import_probe_source_reads_once.rs` — pinned by COUNT not wall clock (25 visits x 2 paths must yield exactly 2 reads + 48 memo hits; an over-cap rejection must also be memoized); counters `PROBE_SOURCE_READS`/`PROBE_SOURCE_HITS` under the existing `SIMPLE_PERF_COUNTERS=1` gate; perf-gate rows `PROBEMEMO *` in `scripts/check/check-perf-regression-tests.shs` (`PASS — 113 mechanism(s) checked, 0 regressed`); audit `doc/09_report/tooling_latency_audit_2026-08-23.md`; bug record extended in `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md` |
| 2026-08-23 | seed HIR import loader (tooling latency) | (this change) | **IMPORTASTMEMO.** `preregister_imported_type_names` and `load_imported_types` (`hir/lower/import_loader.rs`) each did `read_to_string -> CRLF normalize -> Parser::new -> parse()` on EVERY `use` statement naming a module. On a lint of a **two-line** file that is 3,819 successful `.spl` `openat` over 423 distinct files, with `10.frontend/core/ast.spl` **fully parsed 870 times**. Both sites consume the result immutably (`&imported_module.items`) and parsing is deterministic in the file's bytes, so the repeat work is waste. Fixed with `parsed_imported_module()`, a per-PROCESS memo of the parsed `Arc<Module>` (`None` memoizes unreadable/unparseable, which both sites previously recomputed per visit), cleared by `clear_module_cache()`. Deliberately NOT on disk: the `edit src/lib, no build needed` property is load-bearing. Measured interleaved (the box drifted 38s -> 24s for the SAME baseline binary between batches, so only within-batch numbers are quoted): **openat 3,819 -> 676 (5.65x), same 423 distinct files, `ast.spl` 866 -> <=4**; wall median `zca_rows.spl` full **33.86s -> 24.45s (~28%)**; on the trivial fixture **within noise, no improvement claimed** (identical work varied 15.05-27.95s). **Cost stated not buried: max RSS +~110 MB (+19-27%)**, bounded by the import closure rather than by input size. **Three results recorded rather than buried.** (1) **A WRONG first attribution**: the interpreter's import probes (`sibling_might_define_requested_names`, `file_plausibly_provides_names`) look exactly like the defect and were memoized -- correct, kept, and the openat count did not move by ONE call. A wall-clock A/B on this box showed a 1-4s 'improvement' that was pure noise and would have been believed; only the syscall count refuted it. (2) The superlinear lint term this lane was briefed to hunt **no longer exists**: `50.mir/hwir/zca_rows.spl`, documented as `>2400s (killed), exceeds any practical budget`, lints CLEAN in **44.3s** on the deployed seed (>54x), and prefixes of 2/48/293/633/1,170/1,901 lines cost 37.9/36.4/39.2/39.1/37.0/44.3s -- flat. The old cost table misrouted this lane. (3) **`SIMPLE_INTERP_SAMPLE=1` and `SIMPLE_LOADER_TRACE=1` emit NOTHING from the deployed seed** on 37-44s runs -- the binary predates them, and attach profiling is blocked here (`ptrace_scope=1`, `perf_event_paranoid=4`), so a seed redeploy is a prerequisite for the documented in-process route. The attribution above came from `strace` plus a new level-gated read-site trace (`read_trace.rs`, `SIMPLE_READ_TRACE=1`), kept in tree because two lanes have now been defeated by having no attribution. | §20 (seed) | unit test `imported_module_ast_memo_tests::repeated_import_of_the_same_module_parses_it_exactly_once` (20 imports must be 1 parse + 19 hits; a failed import must also be memoized) and integration test `compiler/tests/import_probe_source_reads_once.rs` -- both pinned by COUNT, never wall clock, because this box runs at load 40+; counters `IMPORT_AST_PARSES`/`IMPORT_AST_HITS` and `PROBE_SOURCE_READS`/`PROBE_SOURCE_HITS` under the existing `SIMPLE_PERF_COUNTERS=1` gate; perf-gate rows `IMPORTASTMEMO *` + `PROBEMEMO *` in `scripts/check/check-perf-regression-tests.shs` (`PASS — 119 mechanism(s) checked, 0 regressed`); audit `doc/09_report/tooling_latency_audit_2026-08-23.md`; bug record extended in `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md` |
| 2026-08-23 | docs (authoritative rules file) | (this change) | **Corrected `.claude/rules/commands.md`, which is loaded into every session as authoritative and was actively misrouting lanes.** Its `bin/simple lint` section asserted a superlinear-in-content term and a table ending `zca_rows.spl first 8 fns | 8 | 443 | >2400s (killed)`, with prose calling the file 'exceeds any practical budget' and 'the superlinear term has not been located'. Measured 2026-08-23: the **full** 1,901-line file lints CLEAN in **44.3s**, and cost is **flat** across 2/48/293/633/1,170/1,901-line prefixes (37.9-44.3s) — a ~950x growth in declaration content adds ~6.4s. The file already carried a 2026-08-18 caveat that the table 'MUST be re-measured before use'; that re-measurement has now been done, so the claim is REPLACED rather than re-caveated — a caveat that nobody discharges is how a false number stays authoritative for five days. Rows retained per the file's own 'do NOT delete them' convention, but moved under an explicit **SUPERSEDED 2026-08-23** heading in a collapsed block with the refuted conclusion struck through, so a reader cannot mistake history for guidance. Replaced with the measured truth: the dominant cost is **~37s of FIXED STARTUP**, not per-declaration and not superlinear, root-caused to imported-module re-parsing (3,819 `.spl` opens over 423 files for a TWO-LINE lint, `ast.spl` parsed 866 times) and fixed by `parsed_imported_module()` in `617b58a9ffa` (-> 676 opens), with the explicit warning that **users do not feel it until a seed redeploy**. Also documented the profiling trap that cost this lane hours: **`SIMPLE_INTERP_SAMPLE` and `SIMPLE_LOADER_TRACE` emit NOTHING from the deployed seed** (no output at all on 37-44s runs; the binary predates them, and attach profiling is blocked by `ptrace_scope=1` / `perf_event_paranoid=4`), together with the two routes that DO work — `SIMPLE_READ_TRACE=1` for call-site attribution and `strace -e trace=openat` for counts — plus the instruction to pin perf work by `SIMPLE_PERF_COUNTERS=1` COUNTS rather than wall clock, since identical work measured 15.05-27.95s on this box. Bug record `lint_timeout_hwir_zca_rows_2026-08-17.md` closed: retitled **RESOLVED**, with a status box stating the symptom is gone, that the superlinear term must NOT be hunted a third time, and where the residual fixed cost went. | §20 (seed), §27 (docs) | docs-only; no gate rows (the mechanism rows `IMPORTASTMEMO *` / `PROBEMEMO *` landed with `617b58a9ffa` and stay `PASS — 151 mechanism(s) checked, 0 regressed`); audit `doc/09_report/tooling_latency_audit_2026-08-23.md` |
| 2026-08-23 | bootstrap / phase 2 | `(this commit)` | phase-2 gate defined from the scripts: stage2 = one seed `native-build --entry-closure` of `bootstrap_main.spl`, admitted only after version+negative-control+dual frontend smoke sanity and the struct-receiver proof; the driver's `cmp` steps compare runtime/source snapshots, NOT stage2-vs-stage3 binaries — strict fixpoint is opt-in (`--fixpoint-binary`, A12) and stage4 asserts none. Ranked blockers + load-bearing test set. Measured overturn: `check-stage-binaries-runnable.shs` is ERROR not FAIL — `git ls-files bootstrap` = 0 at origin/main, the four stage binaries are no longer tracked | §27, Phase 1/2 | `doc/03_plan/compiler/bootstrap/phase2_gate_and_blockers_2026-08-23.md` |


### Phase 1 (stage1 bootstrap) state
| 2026-08-23 | reporting / tags | `d6289165bf8` | **in-development became a first-class category, and tags became queryable.** `@tag:` annotations already existed in 1,786 places and `std.test_runner.extract_tags` already parsed every accepted spelling — but NOTHING ever queried them, so an `@tag: in-development` test (expected-fail, skipped by suite runs) was invisible twice over: skipped by the runner and absent from every summary, i.e. indistinguishable from a test that does not exist. New `std.tag_query` reuses that same parser rather than growing a second one, and normalises `_`->`-` so `in_development` and `in-development` are ONE bucket, not two invisible ones. Class swept, not first-hit: `bin/simple stats` text (Failed/Skipped/**In development**, plus an `Other: n (unclassified)` line), `stats --json` (`tests.failed/skipped/in_development/unclassified`), `test_result.md` (`\| In Development \|` row emitted UNCONDITIONALLY — a category that vanishes when empty is one nobody notices when it stops being empty — plus an `\| Other \|` remainder), `pending_feature.md`, and the `src/compiler/90.tools/stats` mirror as well as the live `src/app/stats`. New CLI `bin/simple tags [--tag <name>] [--root <dir>] [--json]` lists all tags with counts or the items carrying one — a top-level command, NOT a `simple test` flag, because it queries source and runs no tests, and because `--tag` exists today ONLY in the Rust runner (`driver/src/cli/test_runner/args.rs:24`) while the pure-Simple runner has no `@tag:` branch at all, so a runner flag would work on one runner and not the other. `FeatureStatus` deliberately did NOT gain a variant (real schema change); the count is threaded from the same test-DB status `test_result.md` reports so the two artefacts cannot disagree. `src/app/test_runner_new/**` and `src/lib/nogc_sync_mut/spec/**` untouched — the runner lane owns the skip semantics | §27 (reporting) | spec `in_development_tag_reporting_spec.spl` (`453ec751c35`): pre-fix with `std.tag_query` removed `outcome=ERROR executed=0`, post-fix `outcome=OK executed=8 passed=8 failed=0`; guard `c5d9c22e1e5` |
| 2026-08-23 | guards / reporting | `c5d9c22e1e5` | **ADVISORY, honestly RED.** Every pre-push guard checks trees, ranges or source; **none reads the NUMBERS in the report**, so `test_result.md` sat at **Total 770 / Passed 0 / Failed 0** — a tracker holding a verdict for none of its 770 tests — with every guard green over it, and `bin/simple stats` printed that as a 0%% pass rate as if it were a measurement. `check-test-summary-reconciles.shs` enforces `passed+failed+skipped+pending+in-development+other == total`, and that `total>0` implies at least one verdict. Fatal selftest (4 fixtures incl. a replay of the exact 770/0/0 shape which must FAIL, and a missing report which must ERROR); 0 metrics read is ERROR, never a pass. Separately found and filed: `test_db.sdn` holds 74 counter rows for 770 tests and its `tests->suites->files` join is skewed (`qemu_user_integration_spec.spl` paired with name `runtime_array_assignment_ssa_spec.spl`), so per-test attribution in the DB cannot be trusted at all. **Stated plainly: the DB-sourced in-development counts are only as trustworthy as the DB, which currently is not; the `simple tags` counts are read from source annotations and are independent of it** | §27 (guards) | `test_db_incoherent_totals_and_broken_file_name_join_2026-08-23.md`; measured `FAIL — 7 metric(s) checked: 770 test(s) recorded, 0 with a verdict` |
| 2026-08-23 | reporting / stats (self-correction) | `85685d2960d` | The `--json` in-development counts from `d6289165bf8` were added to **dead code** and did nothing. `format_json` (`src/app/stats/json_formatter.spl`, called at `dynamic.spl:708`) is unreachable: `run_stats` RETURNS at the `is_json` branch (`dynamic.spl:371`) after printing the `simple.stats.v2` projection, so nothing ~340 lines below it ever runs on that path. The edit compiled and read correctly — it was caught **only by running `stats --json` and finding no such field**, which is the whole argument for executing a surface rather than inspecting it. Dead edits reverted in both the app tree and the `90.tools` mirror rather than left as plausible-looking dead code a later reader would trust. New `app.stats.test_status` is ONE reader for every metric, used by BOTH the text output and `stats_json_v2`, so the surfaces cannot drift; `stats_json_v2` takes the counts as a parameter and stays a pure projection. `unclassified` is derived when the report names no `Other` row, so a silent remainder becomes visible. Both pre-existing `stats_json_v2` callers updated for the new arity | §27 (reporting) | live-path measured twice: `"in_development":2,"unclassified":0` and `"in_development":0,"unclassified":3`, with the text output printing `In development: 2` / `Other: 3 (unclassified)` for the same fixtures; `json_v2_spec.spl` 1/1 green with new assertions |
| 2026-08-23 | reporting / three-state | `254790b3c5d` | **User directive: always show pass / fail / in-development — do not skip.** All three now print UNCONDITIONALLY on every surface owned here, including at zero and including when there is no recorded run (which says so in words instead of implying a measurement): a category that vanishes at zero leaves a reader unable to tell *zero in-development* from *this surface does not track in-development*, and those mean opposite things. **The word "skipped" is retired for it** — a tagged spec EXECUTES and only its verdict is neutralised, so "skipped" misdescribes the mechanism and reads as if work were hidden; a genuine host-unavailable skip keeps its own separate count, now spelled `Skipped (host-unavailable)`, and the two are never merged. Tracks the core lane's three-bucket API from `be0213e30ea`: `in_development` (ran, failed as expected), `in_development_unexpected` (ran, PASSED — ready to promote), `in_development_broken` (could NOT LOAD). **BROKEN gets its own bucket and is never absorbed into the in-development count** — the tag is a claim about the code under test, not a licence for a spec file the loader could not read — and it is deliberately NOT a second reconciliation addend because it already counts inside `failed`; adding it twice would manufacture a phantom remainder. Drift caught **by running it, not by reading it**: renaming the report row silently zeroed the reader that greps `^\| Skipped \|`, producing a phantom `Other: 1`; both spellings are now read | §27 (reporting) | live-path fixtures: `10/6/2 indev 1 BROKEN 2 skip 1` reconciles with no Other line; empty report prints all three at 0 plus `(no recorded run — counts above are zeroes, not measurements)`. Spec `f1967284581` 12/12 (was 8/8); `json_v2_spec.spl` 1/1 |
| 2026-08-23 | reporting / trustworthiness | `254790b3c5d` | **Third defect found and filed rather than papered over: in-development is ABSORBED INTO `skipped` at the source.** The runner neutralises a tagged file by returning `TestFileResult(passed: 0, failed: 0, skipped: expected)` and records **no distinguishing per-test DB status**, so `tests_by_status("in_development")` can never match and the `\| In Development \|` row in `test_result.md` is **structurally zero — not measured, and not a real zero** — while the `Skipped` row silently CONTAINS them. That is exactly the hole the category was created to close, and it cannot be fixed from the reporting side: it needs a runner-side field or status. Until then the report prints an explicit caveat under the summary instead of a confident 0. **Plainly: DB-sourced counts (`stats`, `test_result.md`, `stats --json`) are NOT trustworthy today; `bin/simple tags --tag in-development` is source-derived from `@tag:` annotations and IS.** The runner's classifier itself is correct — the loss happens where the outcome is written back into a struct with no field to hold it | §27 (reporting) | `test_db_incoherent_totals_and_broken_file_name_join_2026-08-23.md` (Update 2026-08-23); gate `0888a90698e` still ADVISORY: `FAIL — 9 metric(s) checked: 770 recorded, 0 with a verdict` |
| 2026-08-23 | reporting (self-correction) | `d38e680c63e` | **My own filed diagnosis was wrong, and the truth is worse.** I reported that in-development specs were being absorbed into `Skipped`. I reasoned from the runner STRUCT — the `ExpectedFailure` arm returns `TestFileResult(passed: 0, failed: 0, skipped: expected)` — and never followed the value to the DB **write site**, which is where the status is actually decided. Measured by the runner lane: `update_test_database` chose the row status with `if file_result.is_ok()`, and a neutralised file has `failed == 0`, so **`is_ok()` was TRUE and the row was written as `passed`** (`neutralised_is_ok=true in_development=2` -> `written_status=in_development` after their fix). So a pre-fix DB does not merely UNDERSTATE in-development, it **OVERSTATES passed by the same specs** — every historical DB-derived pass rate is an **overcount, not an omission**, and an overcount misleads in the reassuring direction. Caveat text in `test_result.md` and the guide corrected; the wrong explanation is not kept beside the right one (it would read as a competing account) but what it claimed and why it failed is recorded, because "reasoned from the struct, never checked the write site" is the reusable lesson. Also recorded: `str_to_status` ends in `case _: TestStatus.Skipped`, so any unrecognised status string is **silently relabelled a skip** — both in-development spellings are explicit cases now, but a future status added without touching that function will be silently mislabelled and will look legitimately skipped. No query change was needed: these surfaces already read both `in_development` and `in-development`, so they report correctly as soon as a run is recorded by a runner carrying `TestStatus.InDevelopment` (not yet at origin/main when this landed). Deliberately NOT built on: the runner lane's still-open `Results:` skipped-count discrepancy — no surface here reads that count | §27 (reporting) | `test_db_incoherent_totals_and_broken_file_name_join_2026-08-23.md` (Update 2026-08-23, rewritten) |
| 2026-08-23 | guards (honesty) | `0af43a6b46c` | **The reconciliation gate I added is BLIND to the defect above, and now says so.** I had been citing `check-test-summary-reconciles.shs` as the reason these numbers can be trusted. Folding in-development into `passed` moves a count between addends — the sum is unchanged, so the gate stays green throughout. A passing reconciliation proves no category was **dropped**; it proves nothing about whether each category was **classified correctly**, and conflating those two is exactly how a gate comes to be trusted for something it never checked. Found the honest way: the first draft of the regression example asserted the folded numbers would FAIL to reconcile, and it failed — the assertion was wrong, not the code. The example now asserts the opposite and states why, so the limit is pinned rather than remembered | §27 (guards) | spec `3ce67def453` 13/13 (was 12/12); gate still ADVISORY, `FAIL — 9 metric(s) checked: 770 recorded, 0 with a verdict` |

**Current run:** run11b, worktree `stage1-clean13`, seed `e5f12c93`, tree sha `a6233953eca`.

**Blockers found and fixed:**
- HIR shard children re-parsed the whole closure; front-end cache scope now split by entrypoint script — `a6233953eca`.
- Dead parse shards left orphaned queue claims, stalling the build; claims are reclaimed and every shard exit logged — `6cedd51faec`.
- Seed interpreter perf: `d30727e74e3` (hot path), `88146e0e7e5` (HIR name index / scope probe), `5ff4999c8e9` (quadratic lexing via per-call array value-type scan).
- `kill_simple_monitor.shs` kills the run unless `SIMPLE_TIMEOUT_SECONDS=0` is set — required for any multi-hour stage1 run.

**Open items:**
- Stage1 runs *fully on the tree-walking interpreter*: the JIT bails at `compiler_services.spl:168`, so no compiled code is executed during stage1. Fix lane in progress (`seed_jit_coverage_self_hosted_compiler_2026-08-21.md`).
- `check-push-must-pass` hook circularity: it requires a bootstrap fingerprint that can only be produced by the bootstrap it gates — record filed: `check_push_must_pass_requires_unobtainable_bootstrap_fingerprint_2026-08-22.md`.
- Remaining Phase 1 records (2026-08-21/22): `bootstrap_main_native_build_stalls_after_source_closure`, `native_build_phases_after_parse_single_threaded`, `native_build_frontend_not_incremental`, `native_build_object_cache_never_persists_entries`, `phase3_hir_import_materialization_time_rss`, `stage1_lexer_hir_fatals_eprint_and_generic_len_helper`, `stage1_untyped_return_reintroduced_by_clobber_llvm_backend`, `stage2_split_impl_modules_missing_from_entry_closure`, `stage3_streaming_hir_owner_crash_after_origin_fix`, `c_runtime_missing_83_codegen_runtime_symbols`, `seed_match_expression_return_arm_statement_cost_cliff`, `seed_filtered_module_dict_rebuilt_per_importer`, `seed_empty_captured_env_allocated_per_import_binding`.
| 2026-08-23 | testing / dev ids | `6b3862dd57b` | in-development work is now **addressable by name**: a spec names its workstream with a second ordinary tag, `# @tag: in-development, dev-id-<id>`. Chosen on evidence, not taste — it needed ZERO grammar change to either extractor (`extract_tags` already splits a `@tag:` directive on commas, `test_manifest_scanner.spl:277`; `spec_tags` already accepts `-` as a tag character, `in_development.spl:_is_tag_char`), so the id is visible to every existing tag consumer **including the Rust runner's `--tag`** (`args.rs:24`) on the day it lands. Rejected: a second `# @dev:` directive (a second parser, and invisible to the one engine that already has tag filtering); `@tag:in-development(id)` and `@tag:in-development/id` (both change the SHARED tag grammar for all 1,022 existing uses, to buy nesting a sibling tag already expresses); `@tag:in-development-<id>` (breaks the documented exact-name match, so both tags would be needed anyway). Selection decides **execution only** — `classify_in_development` still decides the verdict, so the landed neutralise-the-verdict rule is untouched. Default INCLUDES in-development specs; `--no-in-development` is the opt-in exclude, so nothing silently loses the unexpected-pass promotion signal. `bin/simple tags` gains `--dev-ids`, `--dev-id <id>`, `--in-development[=<id>]`, `--no-in-development`, `--paths`; `--paths` composes with `$( )` so the run set works on **both** engines with no runner flag. Native `bin/simple test` flags deliberately deferred — `src/app/test_runner_new/**` is a concurrent lane's, and the rule ships as one shared predicate (`dev_selection_includes`) it can adopt in one call | §20 (tooling) / §27 | `doc/05_design/app/testing/in_development_dev_ids.md`; spec `test/01_unit/lib/tag_query/dev_id_spec.spl` — pure-Simple runner, pre-fix `outcome=ERROR executed=0` rc=1, post-fix `outcome=OK executed=21 passed=21 failed=0`; end-to-end on a 5-file fixture tree: `--dev-ids` -> `auth-rework 2 / parser-hir 1 / Unnamed 1`, `--in-development=parser-hir --paths` -> exactly `c_spec.spl`, `--no-in-development --paths` -> exactly `e_spec.spl` |
| 2026-08-23 | phase-2 blocker B3 / link + guard honesty | `54e12925034` | **B3's "83 codegen-emitted runtime names undefined in `build/simple-core/libsimple_runtime.a`" re-measured as 0** — against a FRESHLY BUILT core-C capsule (`build-core-c-bootstrap-runtime-capsule.shs`, selfcheck pass, 33 checks, 1219 defined symbols), not a months-old artifact: 196 emitted names, 0 undefined. Closed by earlier landings; it *looked* alive only because the guard could never report it. The deeper fail-open (item 3) was already closed by `267db6eb0ca` — the native link now returns `Err` naming every undefined runtime-prefixed symbol, with `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` as a warranted bring-up opt-out (same reasoning as `SIMPLE_ALLOW_UNLOWERED_MIR=1`) and bootstrap lanes exempt. **This commit fixes the guard's own honesty defect:** `git ls-files bootstrap` returns 0 rows (stage blobs untracked), and `check-no-unresolved-runtime-symbols.shs` hard-exited `ERROR — nothing was checked` *before* running the archive half — a permanently uninformative ERROR is indistinguishable from an unwired guard. Zero binaries is now a `binaries=none(...)` STATUS; 0 artifacts in total is still ERROR (fixture (d) unchanged). New fatal fixture (f) with negative control, verified failing pre-fix (rc=2). Post-fix verdict: `PASS — 196 symbol(s) checked across 0 binary(ies) + archive, 0 unresolved`. Open, stated: the binary half has no artifact to judge (untracked + stripped), and the archive half is a lower bound by construction — the link, not a regex, is the authority on what codegen actually emitted | §27 | `stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md` § 2026-08-23; `scripts/check/check-no-unresolved-runtime-symbols.shs` fixture (f) |
