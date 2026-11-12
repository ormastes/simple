# Simple Robust Types, State-Dependent Fields, and Layer Contracts

**Final design and implementation report — 2026-11-12**
**Status:** target design approved in discussion; **not** a claim of completed compiler, interpreter, or LSP enforcement.
**Scope:** Simple language guide, parser/HIR/MIR, compiler safety admission, LSP/MCP diagnostics, embedded NVMe FW, immutable compiler pipelines, and compatibility migration.
**Document contract:** **standalone, single-file final report**. It includes the normative language-guide update, compiler architecture, source-level migration rules, diagnostic examples, testing, performance targets and rollout plan. No linked document is required to implement or review this specification.
**Language guide (canonical text of §2):** [robust_semantic_absence.md](../../../07_guide/language/robust_semantic_absence.md).

## 1. Final decision

The central rule is **a later layer must receive a type that proves every property it requires**. A missing field may be unknown in an early layer, but it must be impossible to pass the early representation into a layer that requires the field. Safe code does not achieve this by assigning `nil`, guessing a default, repeatedly unwrapping `Option<T>`, or asserting that the value probably exists.

Use four orthogonal mechanisms:

1. **Concrete/default inputs and meaningful payload enums** for the public API; no raw generic absence in ordinary robust code.
2. **Phase-specific types or `T<State>` typestate** when data gains guarantees after parsing, validation, mapping, or another layer transition.
3. **`NotInit<T>` backing storage plus compiler-verified initialization** only where allocation precedes initialization; never treat it as a missing-value domain model.
4. **Dynamic payload enums** when an asynchronous or external transition genuinely changes state at runtime, with typed checked transitions and epoch/ownership protection.

No new `check`, `require`, `none`, `nonnull`, or state-specific field keyword is required for the first implementation. Reuse generic types, payload enums, `match`, `Result<T,E>`, and the already tested refutable `val PATTERN = expr else:` grammar. `NotInit<T>` is the proposed canonical spelling for the wrapper/type; the parser/runtime currently have other *no-initializer* behaviors and must not be assumed to implement this type already. Earlier documents use `notinit<T>` and informal `NoInit`/`NonInit`; normalize them when this feature is implemented.

### Representation choice: cost, robustness, and applicability

| Mechanism | Good use | Robustness | Steady-state memory / CPU | Cost/limitation |
|---|---|---|---|---|
| Concrete `T` | Required argument or field | Maximum if `T` invariant holds | Same as `T` | Caller must supply a valid `T` |
| Explicit meaningful default | Omitted argument has a real documented value | Strong if default is semantically valid | No optional tag; argument may be compile-time defaulted | Cannot invent default or silently change behavior |
| Payload `enum` | `Flush` vs `Read`, `Connected` vs `Failed` | Impossible invalid cross-variant field combinations | Usually discriminant + maximum payload, subject to niche optimizations | Dynamic dispatch/match may cost a branch |
| Distinct `Parsed` / `Resolved` types | Incremental validation stages, compiler HIR/MIR | Layer contract checked statically | Can use zero-copy typed handles | Converting entire records may copy data |
| `T<State>` with private transition | Shared pool/arena slot and static lifetime stage | Strong only with exclusive, stable proof | Marker can occupy zero bytes; no stage check after transition | Generic code size; alias/async invalidation complexity |
| `NotInit<T>` | Storage allocated before initialization | Safe only with definite-assignment/proof | No tracking tag when proof is static; **still reserves `sizeof(T)`** | Without proof, reading it is unsound |
| `Option<T>` | Legacy compatibility or reviewed HAL/interpreter boundary | Absence must be handled; easy to misuse as vague status | Niche optimization may make it free, **not guaranteed** | Rejected in ordinary robust code |
| Runtime `assert` | Debugging, provable redundant invariant | Not a general no-panic safety proof | May branch/raise | Must not manufacture a static state guarantee |

The *static state marker* may be zero-cost; the *necessary runtime validation at a transition* is not free. A transition can validate once and thereafter avoid redundant per-layer checks. State-specific API specialization can increase code size even when runtime state metadata is erased.

## 2. Language policy: public APIs, `Option`, `None`, `nil`, and pointers

### Public surface

- **`ROB-OPT-001`:** public function, method, constructor, callback and generated setter input must not expose `Option<T>`.
- **`ROB-OPT-002`:** exported attribute/property and generated getter must not expose `Option<T>`.
- **`ROB-OPT-003`:** robust-mode ordinary safe code ultimately rejects raw optional types in return values, locals, nested collection/tuple/function types, aliases and `T?` sugar too. Public inputs/attributes are the first priority, not the only eventual targets.
- `Option<T>`, `T?`, `List<Option<T>>`, type aliases, generic specialization, re-exports and inferred public accessors **all count**. A nominal domain type that happens to contain a valid state enum is not automatically an `Option` exemption.
- The only planned raw-optional exceptions are **explicitly reviewed HAL/interpreter declaration capabilities**. Neither a path name nor `--engine=interpreter` grants a capability. A public adapter should translate the boundary value into a semantic domain result as early as possible.
- Do not promote genuinely private fields into public findings merely because their containing class is exported. Resolve actual effective visibility from `__init__.spl` and generated members.

### Required distinctions

| Term | Meaning | Robust-safe usage |
|---|---|---|
| `None` | The enum variant of a typed legacy optional | `case None:` only when matching a proven `Option<T>` at an allowed compatibility/boundary site; **not** a new raw absence literal |
| `nil` | Raw nil/null literal | Rejected in safe source including assignment, return, comparison and `case nil:`; only explicit `unsafe:` / `danger:` |
| `NotInit<T>` | Reserved storage before the first valid `T` is constructed | Private/pool/stack backing only, with compiler proof before reading; not a substitutable `T` |
| `Err(E)` / meaningful enum | Failure, cancellation, disconnected, unavailable, etc. | Preferred for explicit domain semantics |
| `T = default` | Valid and documented contract default | Allowed only after checking default constructor, invariants, callers, behavior and ABI |

Do not rewrite `nil` tokens into `None` tokens mechanically: their current representation and source meaning differ. Do not rewrite `Option<T>` into `NotInit<T>`; initialization progress and domain absence are different concepts.

### Canonical Simple language guide: choosing an input type

The following examples are **proposed design examples**, not claims that every syntax shape already passes native and interpreter acceptance. They are the normative guide for new robust APIs.

**Rule A — a required argument must be a required value.**

```simple:skip
# Legacy API: callers can omit a meaningful requirement.
pub fn connect(host: Host, timeout: Option<Duration>) -> Result<Session, Error>

# Robust API: timeouts are always concrete.
pub fn connect(host: Host, timeout: Duration) -> Result<Session, Error>
```

**Rule B — if a documented default is meaningful, use a typed default.**

```simple:skip
pub fn connect(host: Host, timeout: Duration = 5_s) -> Result<Session, Error>
```

A default must be proved valid for this function: neither `0`, `false`, an empty string, nor an arbitrary `T.default()` is a general replacement for `None`. An LSP quick fix may suggest a class's *actual* default constructor only after resolving its declaration and checking that the behavior is intended. A default may require a cross-file API-compatibility review.

**Rule C — if omission selects a mode, express that mode as a value enum.**

```simple:skip
enum TimeoutPolicy:
    Infinite
    Immediate
    After(Duration)

pub fn connect(host: Host, policy: TimeoutPolicy = After(5_s))
    -> Result<Session, ConnectionError>
```

Each constructor has a meaningful interpretation. This is not interchangeable with an optional duration whose absence may mean different things in different callers.

**Rule D — if the operation is different, split the API instead of overloading `None`.**

```simple:skip
# Discouraged:
pub fn send(data: Buffer, destination: Option<Address>) -> Result<Receipt, SendError>

# Prefer distinct operations when omission really means broadcast:
pub fn send_to(data: Buffer, destination: Address) -> Result<Receipt, SendError>
pub fn broadcast(data: Buffer) -> Result<Receipt, SendError>
```

**Rule E — public attributes follow the same restriction as parameters.**

```simple:skip
# Discouraged: many invalid combinations are representable.
pub struct Connection:
    socket: Option<Socket>
    error: Option<ConnectionError>

# Robust: the tag selects valid payloads.
pub enum Connection:
    Disconnected
    Connecting(RequestId)
    Connected(Socket, Session)
    Failed(ConnectionError)

match connection:
    case Connected(socket, session): use_connection(socket, session)
    case Connecting(request): wait_for(request)
    case Disconnected: reconnect()
    case Failed(error): report_failure(error)
```

The same prohibition covers generated public getters/setters, constructor fields, callbacks, traits/interfaces, exported aliases and fields visible through a layer/feature export. The attribute is **not globally present** on the enum; `socket` is present only inside the `Connected` case. For a statically known lifecycle, use a state-specific type that directly exposes a non-optional `socket` accessor.

**Rule F — use typed failure results rather than generic absence for a validation failure.**

```simple:skip
enum AgeError:
    TooYoung(i64)
    TooOld(i64)

struct Age:
    value: i64

fn make_age(value: i64) -> Result<Age, AgeError>:
    if value < 0: return Err(TooYoung(value))
    if value > 150: return Err(TooOld(value))
    Ok(Age(value: value))
```

Unlike `Option<Age>`, the error states why construction was rejected. Do not imply that every generic `Option` return should be replaced by `Result` with a fabricated error: where there are several meaningful success/absence states, a domain payload enum may be clearer.

**Rule G — choose `None` and `nil` by semantics, never as interchangeable spellings.**

```simple:skip
# Permitted only at an audited optional compatibility/boundary site:
match legacy_option:
    case Some(value): consume(value)
    case None: handle_legacy_absence()

# Not valid in ordinary robust-safe source:
val value = nil
if pointer == nil: return nil
match legacy_option:
    case nil: handle_legacy_absence()

# Raw pointer interaction must be in an explicit unsafe/boundary region,
# followed by a checked conversion to a non-null safe reference.
```

`None` remains a typed `Option` variant, with capital **N**; it is not a new universal absence keyword. If a normal robust component needs `NotFound`, `Disconnected`, `Pending`, or `Unmapped`, declare the **domain-named state**. Suppressing `NIL-UNSAFE-001` by replacing literal text with `None` without type resolution is forbidden.

**Rule H — when a layer discovers a required attribute later, change the type at that boundary.**

```simple:skip
fn resolve(node: ParsedNode) -> Result<ResolvedNode, ResolveError>
fn check_type(node: ResolvedNode) -> Result<TypedNode, TypeError>
fn lower(node: TypedNode) -> MirNode

val parsed = parse(source)
match resolve(parsed):
    case Ok(resolved):
        match check_type(resolved):
            case Ok(typed): lower(typed)
            case Err(error): report(error)
    case Err(error): report(error)
```

The `symbol` or `type_id` fields need not exist in `ParsedNode`. They **must** exist in the representation accepted by their next layer. A flow guard may narrow an enum locally, but a publicly callable layer is stronger when its parameter type itself carries the guarantee. Use `Result<Next, E>` on a fallible transition, not `assert` to cast `Old` into `Next`.

**Rule I — storage reserved before initialization is not optional data.**

```simple:skip
# Private backing storage inside a pool, NOT an exported public field:
struct CommandSlot:
    dma: NotInit<DmaBufferHandle>

# A checked transition initializes dma, then returns a Ready handle.
fn prepare(cmd: Command<Validated>) -> Result<Command<Ready>, DmaError>
fn execute(cmd: Command<Ready>) -> Completion
```

The representation must be backed by real all-path proof and private constructors. A later `Ready` method cannot simply call `.assume_init()` on unverified memory. If an asynchronous DMA engine can revoke the state, the proof must be invalidated or replaced with a runtime enum; retaining a stale static handle is an error.

### Guide migration checklist and examples

Before changing an existing public declaration:

1. **Find all users:** call sites, derived/generated constructors/getters, interfaces, aliases, macros and re-exported entry points.
2. **Identify semantics:** does absence mean a valid default, another operation, a transient state, a failure, an FFI null or merely not-yet-initialized storage?
3. **Choose one design:** concrete `T`; explicit valid default; payload enum; split API; `Result`; state-specific layer type; private `NotInit<T>`; or reviewed HAL/interpreter adapter.
4. **Prove each transition:** exact field initialization, variant exhaustiveness, stable ownership, mutation and async invalidation, ABI and cache revision.
5. **Offer and review multiple fixes:** all alternatives with caller impact, not a single generic `unwrap()` or automatic `None` replacement.
6. **Verify behavior:** native/interpreter parity, SSpec tests, no-panic/invalid-state rejection, memory layout and hot-path CPU before enabling Deny.

This section is suitable as the canonical text of `doc/07_guide/language/robust_semantic_absence.md` and the relevant examples in `type_system.md` and `error_handling.md`; the rest of this file specifies the compiler work necessary to make those rules enforceable.

### Pointers and pool indices

- `&T` / `&mut T`: safe references are non-null, initialized, and valid for the required lifetime. Their source may be an FFI pointer only after a checked boundary conversion.
- `*T`: raw pointer with nullable/unchecked representation only in explicit unsafe/FFI handling; cannot be implicitly passed as a safe reference.
- `Index<Owner>`: proof of a particular collection identity, bounds and structural version, with invalidation after relevant mutation.
- `Handle<Region, State>`: index-pointer to a pool plus generation/region and optionally static stage marker; the handle must not authorize access to a recycled slot. Generation and region metadata may fit existing handle bits, but a verification check still costs time when required.
- Rechecking can be eliminated only while owner, length, epoch, alias permissions and generation remain stable. DMA/hardware reset invalidates any dependent proof.

## 3. Layer-dependent required fields: compiler AST to MIR

The field that is unknown in layer N should be **mandatory by type** in layer N+1. Prefer a monotonic representation or immutable typed view, not `Option` fields carried throughout the pipeline.

| Stage | Representation | Guaranteed after transition | Boundary failure |
|---|---|---|---|
| Parser | `ParsedNode` | syntax, span, node identity | parse diagnostic/recovered parse node |
| Name resolver | `ResolvedNode` | symbol identity and valid lookup | `ResolveError` |
| Type checker | `TypedNode` | concrete validated type, effects/state facts | `TypeError` |
| HIR validation | `ValidatedHir` | attributes/invariants required for lowering | validation diagnostic |
| MIR validation | `ValidatedMir` | well-formed instructions and checked contracts | MIR diagnostic |
| Backend | typed `ValidatedMir` input | required operand types and structural properties | backend/codegen error |

**Proposed API sketches (design, not currently certified syntax):**

```simple:skip
struct ParsedNode:
    id: NodeId
    span: Span

struct ResolvedNode:
    id: NodeId
    symbol: SymbolId       # never optional in this type

struct TypedNode:
    id: NodeId
    symbol: SymbolId
    type_id: TypeId         # never optional in this type

fn resolve(node: ParsedNode) -> Result<ResolvedNode, ResolveError>
fn typecheck(node: ResolvedNode) -> Result<TypedNode, TypeError>
fn emit_mir(node: TypedNode) -> MirNode
```

`emit_mir(ParsedNode)` is a **compile error**. A failed resolution is a typed `Err`, not a partially filled `ResolvedNode`. The next layer does not accept a value with "maybe resolved" attributes. Parser recovery may retain malformed nodes, but only inside a recovery type/variant that cannot cross the strict validation gate.

For Simple's existing **immutable AST/HIR/MIR caches**, physically copying every node is undesirable. Implement phase-specific lightweight handles over stable arena/attribute tables (or small separate immutable payload records):

```simple:skip
struct NodeRef<Phase>:
    region: RegionId
    id: NodeId
    revision: RevisionId

fn lower(node: NodeRef<Typed>) -> MirNode
```

The backend accesses state-guaranteed typed metadata through the `Typed` view. The typed view's constructor is private to the successful validation transition. Cache hits may restore the view **only after** validating source digest, semantic policy revision, owner/region, metadata schema and proof receipt. Incremental edits invalidate dependent views. If the tree changes, no stale typed view is reusable solely because `NodeId` happens to match.

Avoid a Cartesian explosion (`Node<Parsed, Resolved, Checked, Allocated, Optimized,...>` for every field). Define a small number of meaningful stage gates; use separate side tables for fine-grained facts and compact metadata.

## 4. NVMe FW: command phases and physical storage

The same principle applies to SQE decoding and firmware queues:

```text
RawSqe --decode--> DecodedCmd --validate--> ValidatedCmd
                                 | invalid -> NVMe error completion
ValidatedCmd --map/prepare--> ReadyCmd --submit--> InFlightCmd
                             | failure -> typed resource/error completion
InFlightCmd --hardware event--> Completed | Aborted | Reset
```

**Stage-specific payloads:**

```simple:skip
enum ValidatedCmd:
    Read(ValidatedRead)
    Write(ValidatedWrite)
    Flush(ValidatedFlush)

struct ValidatedRead:
    namespace: NamespaceHandle
    lba: Lba
    count: BlockCount

struct ReadyRead:
    command: CommandHandle
    dma: DmaBufferHandle

fn prepare_read(cmd: ValidatedRead) -> Result<ReadyRead, DmaError>
fn execute_read(cmd: ReadyRead) -> Completion
```

`Flush` has no fake DMA buffer or public optional buffer. When command structs must remain in a fixed-size zero-allocation pool, the *private physical slot* may contain `NotInit<DmaBufferHandle>` and a typed `Command<Ready>` carries the proof that the appropriate slot was initialized. The public `Ready` view never returns `NotInit` or `Option`.

Enforce these conditions:

1. The pool slot is initialized before its `Ready` handle can be constructed; the only constructor is an authorized transition that consumes the previous handle.
2. A read of an uninitialized slot is rejected even if another control-flow branch usually initializes it.
3. Queue send/receive transfers exclusive ownership (or an explicitly verified permission); old stage handles cannot continue using the command.
4. A reset, cancellation, DMA completion, concurrent engine update or slot recycle may change runtime state: represent genuinely changing states with a **payload enum/runtime tag** and invalidate dependent static proofs. Do not claim `Command<Ready>` forever when hardware can change it independently.
5. A handle from an external engine, wire message, persisted cache, or dynamically loaded code does not become trusted merely through a generic type cast. Revalidate external data and version/epoch identity at the ingress boundary.
6. Keep ordinary firmware hot paths allocation-free and prevent repeated checks after a successful, stable transition. Async completion and lifecycle checking may still require a branch or generation comparison.

## 5. `NotInit<T>`: safe zero-tag initialization, not nil-defaulting

**Current repository hazard:** the source parser currently synthesizes zero values or `nil` for some bare `var name: Type` declarations. For named globals it builds `EXPR_NIL_LIT`, and `test/01_unit/compiler/parser/module_noinit_named_nil_parity_spec.spl` explicitly asserts parity between an omitted initializer and `= nil`. Scalars may silently read as zero. This is **legacy behavior, not robust initialization proof**.

Therefore implement the change in two steps:

1. **Separate representation**: add an AST/HIR concept for `UninitializedDecl` distinct from an actual source `NilLit`. Preserve legacy behavior under a compatibility profile while proving new robust semantics. Never infer safety from the old synthesized nil/zero initializer.
2. **Definite assignment**: use a fast forward CFG/MIR dataflow pass with `Uninitialized`, `Initialized`, `Maybe` facts per local/field, including returns, branches, loops, destructuring, moves, callbacks and async suspension. At a merge, a read is allowed only if **every** reachable incoming path initialized that location. Refuse unwarranted promotion across aliases and concurrency.

**Proposed robust spelling and semantics:**

```simple:skip
var dma: NotInit<DmaBufferHandle>  # explicit storage; not a valid DmaBufferHandle
dma = allocate_dma(...)           # checked transition, not nil fill
# Access as T is legal only after compiler proves this assignment on every path.
```

Do not expose `NotInit<T>` as a public API argument or attribute simply to circumvent the `Option<T>` ban. Its raw-storage wrapper may be used privately; a public interface should receive or return the *completed phase type*. If initialization can fail, return `Result<Ready, InitError>` and keep the unready object in a separate failure path.

**Layout:** the wrapper reserves the storage/alignment needed by `T`, but a statically established initialization proof need not add a flag or branch. Do not advertise this as universal zero-memory initialization: storage still exists, and runtime proof is needed when pointer aliases or hardware can mutate state. A non-trivial destructor/drop must never run for an uninitialized payload.

## 6. Static assertions, narrowing and transitions

1. Prefer **`match`** for enums with runtime-variant payloads and exhaustiveness checking.
2. Prefer **refutable `val PATTERN = expr else: return Err(...)`** for a local recoverable state guard, when supported for the given pattern in all backends.
3. Prefer **`fn validate(old) -> Result<Next,Error>`** for a public/cross-layer guarantee; only successful constructors may create `Next`.
4. Permit compiler-produced flow-sensitive narrowing only on stable, immutable or exclusively borrowed values. A branch proof cannot survive an aliasing mutation, relevant `await`, DMA reset, or unknown callback.
5. Do not let `assert state == Ready` automatically retype an object: current `assert` lowers to raising `__assert` in `src/compiler/10.frontend/core/parser_stmts.spl`, which conflicts with no-panic robust code. A provable assertion may be eliminated; a non-provable condition must use a typed recoverable failure branch. `assume`/unchecked promotion is `unsafe` or verification-only, never an automatic LSP fix.

The parser already tests `val Some(inner) = value else: return ...` in `test/01_unit/compiler/parser/refutable_val_else_spec.spl`. Generalizing the proof to all enum variants and `T<State>` still needs real HIR, MIR, native and interpreter acceptance tests. Do not document untested grammar as production-complete.

## 7. Compiler architecture and exact edit points

| Layer / path | Required work | Performance strategy |
|---|---|---|
| `src/compiler/10.frontend/core/parser_stmts.spl`, `parser_decls_use.spl`, `_Ast/*` | Preserve **source** `nil` vs omitted initializer vs explicit `NotInit`; source span, type and macro origin; avoid synthesized proof | One-pass syntax distinction, no additional parser backtracking |
| `src/compiler/10.frontend/core/hir_types.spl`, `hir/lowering.spl` | Carry resolved phase, state-variant payload, effects and typed field requirements; preserve opaque `NodeRef<Phase>` metadata | Immutable compact IDs + side-table summaries |
| `src/compiler/35.semantics/lint/semantic_api/*` | Add **live integrated** public-surface visitor for recursive `Option` detection, including aliases, generated accessors and exports | One resolved declaration/type graph walk; memoize normalized types |
| `src/compiler/35.semantics/safety_checker*.spl` | Define stable state-refinement facts, parameter/field state preconditions, transfer effects and invalidation | Local CFG summaries; no default whole-program SMT |
| MIR lowering and driver (`src/compiler/10.frontend/core/mir/*`, `src/compiler/80.driver/*`) | Verify all-path initialization; gate typed HIR/MIR consumers; prevent unchecked transition, missing payload access and stale proof | Worklist with compact bitsets and incremental digest cache |
| `src/compiler/90.tools/lint/rules/nil_outside_unsafe_rule.spl`, `_LintMain/*`, driver safety policy | Retain current compatibility warning; replace token-only decisions with semantic AST/HIR evidence for hard-deny, without false positives | Cheap lint for early UX; semantic admission is authoritative |
| `src/compiler/90.tools/fix/*`, CLI/LSP/MCP diagnostic model | Shared source spans, multiple semantic candidate fixes, lazy resolved code actions, stale-edit guard, multi-file previews | Cache fix plans; do not scan whole tree on each keystroke |
| Interpreter, native and FFI boundary | Apply same robust policy and staged guarantees independent of execution engine; admit reviewed HAL/interpreter boundary only | Single policy receipt reused across engines |
| SSpec runner + build cache | Test transitions, failure paths and proof invalidation; key caches on policy/schema/export digest | Incremental fixture-first checks; selective CI |

### Typed proof representation

Use a small local abstract state per tracked place:

- `init`: `Uninitialized | Initialized | Maybe`.
- `variant`: `Known(VariantId) | Unknown`.
- `phase`: `Parsed | Resolved | Typed | Ready` where meaningful; do **not** attach an exhaustive product of flags to every node.
- `authority`: owner/region/generation, current revision and stable-borrow epoch as needed.
- `effects`: whether an operation may mutate the place, invalidate the snapshot, transfer ownership, or suspend.

At branch joins, retain only facts true along **every reachable path**. A static state constructor requires proof of field initialization, invariant validation and authority; its implementation may be specialized while the marker is erased. Reuse immutable per-function summaries in the compiler, interpreter, LSP and MCP; invalidate with source, export, generic, macro, effect or policy changes. Reserve interprocedural and concurrent exhaustive proof for `analysis`/CI; unknown effects require runtime validation or rejection, not an unsound assumption.

### Compiler diagnostics (stable proposed codes)

| Code | Condition | Key guidance |
|---|---|---|
| `ROB-OPT-001` | Public input/constructor/callback contains raw optional | Concrete `T`, valid default, semantic enum, API split |
| `ROB-OPT-002` | Public field/property/generated accessor contains raw optional | Payload variant or state-specific getter/field |
| `ROB-OPT-003` | Other raw optional in ordinary robust code | Domain enum or recoverable `Result` transition |
| `ROB-OPT-004` | Spoofed/unverified HAL/interpreter allowance | Explicit audited boundary conversion |
| `NIL-UNSAFE-001` | Raw `nil` in safe expression/pattern/comparison | Typed replacement chosen from actual resolved semantics |
| `ROB-INIT-001` | Read from possibly uninitialized storage | Initialize on all paths or change control flow |
| `ROB-INIT-002` | `NotInit<T>` escapes into a completed/public type | Validated transition and private backing storage |
| `ROB-STATE-001` | Field used before its required phase or variant | Produce required phase or branch on a payload enum |
| `ROB-STATE-002` | Illegal/unverified state transition or constructor | Use registered checked transition |
| `ROB-STATE-003` | Proof invalidated by mutation, async, alias, reset or recycled pool slot | Revalidate or acquire new stable handle |
| `ROB-INDEX-001` | Index/handle lacks owner, bounds or generation proof | Checked index/handle constructor or renewed proof |

All diagnostics should carry exact expression and declaration spans, expected vs actual state, missing guarantees, original alias paths, policy revision, and source of invalidation. A public API error must report its externally reachable path (including re-export and generated getter) rather than an isolated line match.

### Example shared error and ranked quick fixes

```text
ROB-STATE-001: emit_mir() requires TypedNode; found ResolvedNode.
Missing: type_id, validated effect/type facts.
At: backend/emit.spl:42:13

Fix 1: Call typecheck(node) and handle Err(TypeError) before emit_mir().
Fix 2: Change this layer's signature to accept ResolvedNode only if
       it is responsible for checking types.
Fix 3: Split the function into separate Resolved and Typed handlers.
Fix 4: Add a state-specific wrapper/typed view backed by the same NodeId.
```

Each fix carries preconditions, risk, confidence, affected callers, preview, and post-edit test plan. **Never** silently invent `T.default()`, wrap a failed init in `NotInit<T>`, attach HAL capability, replace `nil` with `None`, or change public signatures across files without developer choice. The LSP should present several actionable fixes; only provably semantics-preserving local changes qualify for unattended fix-all.

## 8. Compatibility, severity and policy receipt

**W — compatibility and inventory (first):**

1. Keep legacy programs building while robust/critical emit warnings for `nil`, `Option` public inputs/fields, ambiguous implicit initialization and unsafe state transitions. Do not escalate unrelated existing safety lints globally.
2. Baseline findings by declaration ID and policy digest, show all new findings, measure false positives. Continue warning legacy `var x: T` until its zero/nil initializer semantics and usage are distinguished.
3. Introduce `NotInit<T>` and phase-specific APIs behind opt-in acceptance tests. Existing parser and module tests are **regression evidence** of the previous behavior, not proof that robust semantics already exist.
4. Audited HAL/interpreter exception manifests and rule revisions are SDN; use JSON only for required external tooling protocols.

**E — robust error gate (only after evidence):**

1. Raise only verified `ROB-OPT`, `NIL-UNSAFE`, `ROB-INIT` and `ROB-STATE` rules to Deny in robust/critical/verified profiles. Do not globally flip driver safety severity.
2. Prevent native/interpreter/HIR/MIR/cache admissions without matching policy receipt and required proof. Reject malformed or forged boundary exemptions.
3. Preserve non-robust/older modules through explicit, versioned compatibility adapters; no invisible ABI rewrite. Record diagnostics and quick fixes for migration.
4. Publish migration guide and warning census before the error release. CI performs high-cost proof and performance checks only where configured.

## 9. Acceptance tests: compiler and NVMe FW

| ID | Acceptance scenario | Expected result |
|---|---|---|
| S-01 | `ParsedNode` passed directly to `emit_mir(TypedNode)` | Compile-time state mismatch with suggested transition |
| S-02 | `ResolvedNode` omits required `symbol_id` | Constructor/transition rejected; no partial valid object |
| S-03 | Resolution/typecheck fails | Typed `Err`; failed value does not enter stricter layer |
| S-04 | `NotInit` initialized only on one branch; read after join | Error even if common path initializes |
| S-05 | `NotInit` initialized on all paths; read after join | Pass without steady-state init tag |
| S-06 | Validation followed by alias mutation/`await`/revision change | Previous refinement invalid; checked recovery required |
| S-07 | NVMe invalid NSID/LBA/metadata, DMA failure | Error completion; no construction of `ReadyRead` |
| S-08 | `Flush` and `Read` share command dispatch | Variant-specific fields; no dummy or optional DMA field |
| S-09 | Reset and slot reuse while older handle is outstanding | Generation/epoch mismatch; no stale access |
| S-10 | Compiler cache restores typed view after source edit | Invalidate stale proof; only verified receipt can promote |
| S-11 | `None` pattern on permitted legacy `Option`, raw `case nil` in safe code | Typed `None` case accepted as allowed; raw `nil` diagnosed |
| S-12 | Public param, field, getter, alias, nested generic, re-export | All correctly flagged by resolved API walker |
| S-13 | Valid/default constructor exists vs absent | Offer actual default only when semantic and syntactic evidence supports it |
| S-14 | Phase W then phase E; interpreter/native, 32/64-bit | Same admissions; warning/error toggled by versioned rule gate |
| S-15 | Pooled typed handle vs old raw command hot path | No new heap allocation; benchmark stage tracking, queue throughput and RSS |
| S-16 | GPU-friendly parser and incremental HIR cache | No new parsing ambiguity or unnecessary global scans; same incremental correctness |

Add parser/HIR/MIR/borrow/alias/async, interpreter/native, warning/error and LSP quick-fix unit tests; SSpec acceptance scenarios for compiler and NVMe FW, plus property/fuzz tests for arbitrary state-transition sequences. In analysis/CI builds, test invariant proofs against race/reset/reuse scenarios and ensure no new runtime panic paths.

**NFR gates (proposed, verify against measured baseline):** no per-command allocation introduced in NVMe FW; no persistent stage tag for exclusive static typestate; no unproved branch elimination; no new global solver on normal compiler hot path; incremental flow-check cost measured (target <=3% warm compile CPU, <=5% peak RSS on representative projects, to be negotiated after baseline); generated-code size and 32/64-bit ABI/layout deltas reported. Failing budgets require optimization or an explicit revised target, never an undocumented exemption.

## 10. Execution order, options, and risks

| Phase | Deliverable | Estimate | Primary risk / mitigation |
|---|---|---|---|
| P0 | Final guide policy, current behavior audit, boundary/visibility map, failing acceptance specs | Small–medium | Legacy nil/no-init conflation -> distinguish source syntax before enforcement |
| P1 | Semantic public API walker (`ROB-OPT`) integrated with driver, warning census | Medium | Aliases/generated exports missed -> traverse resolved export closure |
| P2 | Source nil vs omitted init AST/HIR split; `NotInit` proof and private storage transitions | Large | Breaks compatibility -> warning, explicit compatibility profile, all-path tests |
| P3 | Phase-specific typed handles, enum narrowing and transition admission, invalidation | Large | Stale proof across aliases/async -> ownership/epoch checks |
| P4 | MIR/backend optimization, index/handle contract, native/interpreter parity | Medium–large | ABI/code-size cost -> layout benchmarks and identical policy receipts |
| P5 | Shared diagnostics, multiple LSP/CLI/MCP fixes, guide migration automation | Medium | Unsafe automatic rewrite -> semantic preconditions and cross-file preview |
| P6 | Robust rule-by-rule Deny gate after SSpec/perf and false-positive evidence | Medium | Ecosystem breakage -> versioned adapters and sunset schedule |

**Alternative considered:** annotate individual fields with `@required_after(State)` or a new `when State: field` grammar. It is compact (pro), but introduces parser/GPU grammar work, many implicit cross-file proof dependencies, and unclear field-layout rules (cons). **Decision:** defer. Start with existing generic type/enum syntax and private checked constructors (moderate parser work, medium–large semantic work), then introduce a declarative sugar only if real code and measurements justify it.

**Alternative considered:** add only `assert`/runtime tags. Easy to prototype (pro), but cannot eliminate unsafe states in downstream public signatures and introduces per-use panic/branch risk (con). **Decision:** do not use as the safety basis.

**Alternative considered:** put `Option<T>` in every intermediate node and remove it late. Existing syntax and quick migration (pro), but makes missing fields representable and puts repeated checks in all downstream layers (con). **Decision:** reject for robust public/layer contracts.

## 11. Verified baseline, missing implementation, and stopping criteria

Repository evidence inspected during preparation:

- `src/compiler/10.frontend/core/parser_stmts.spl`: bare local `var name: Type` synthesizes defaults for certain types; `assert` lowers to raising `__assert`.
- `src/compiler/10.frontend/core/parser_decls_use.spl`: some bare module globals synthesize `expr_nil_lit` or array initializers.
- `test/01_unit/compiler/parser/module_noinit_named_nil_parity_spec.spl`: explicitly requires nil parity for legacy named globals; test header says **UNRUN**.
- `test/01_unit/compiler/parser/refutable_val_else_spec.spl`: has concrete `val Some(inner) = value else: return ...` syntax.
- `src/compiler/35.semantics/lint/semantic_api/checker.spl`: primitive surface checker is documented as **standalone, not integrated into live lint**; it is not the proposed resolved optional walker.
- `src/compiler/90.tools/lint/rules/nil_outside_unsafe_rule.spl`: a warning/lint path exists; it is a source scan, not sufficient as authoritative typed safety admission.
- `doc/07_guide/language/type_system.md`, `error_handling.md`, and `robust_semantic_absence.md`: migration policy exists but contains historical optional/nil examples requiring clear compatibility labeling.

**What has not been implemented/proven:** `NotInit<T>` as a canonical runtime/type-system wrapper; type-level `NodeRef<Phase>` and transitions; resolved public `Option` checker and exemption receipts; all-path initialization/state proof; reliable full LSP code actions; mandatory robust Deny across both engines; NVMe pool zero-cost layout and end-to-end benchmarks. Do not mark any of these as done based on the design examples.

**Finish only after:** (1) warning migration inventory and approved defaults/exceptions, (2) passing failure/success/ABI/alias/reset SSpec acceptance, (3) native/interpreter equivalence and incremental cache tests, (4) no new unsafe/panic or queue hot-path allocation, (5) measured compiler and FW NFRs, (6) guide/diagnostics consistently document current supported grammar, and (7) a reviewed rule-by-rule error gate. Until then the status is **design complete; implementation pending**.

## 12. Primary language and research sources

- [Rust Embedded Book: Typestate Programming](https://doc.rust-lang.org/beta/embedded-book/static-guarantees/typestate-programming.html); [Zero-Cost Abstractions](https://doc.rust-lang.org/stable/embedded-book/static-guarantees/zero-cost-abstractions.html).
- [Rust `MaybeUninit<T>` documentation](https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html): representation without tracking, and the safety obligation to prove initialization.
- [Rust Compiler Development Guide: AST/HIR/MIR overview](https://rustc-dev-guide.rust-lang.org/overview.html) and [HIR](https://rustc-dev-guide.rust-lang.org/hir.html).
- [SPARK type contracts / record discriminants](https://docs.adacore.com/spark2014-docs/html/ug/en/source/type_contracts.html).
- [Typestate-Oriented Programming, OOPSLA 2009](https://cs.ioc.ee/ewscs/2010/mycroft/aldrich-etal-oopsla09comp.pdf); [Liquid Types, PLDI 2008](https://patrickrondon.com/research/papers/liquid-types-pldi08.pdf); [Kotlin specification: smart-cast stability](https://kotlinlang.org/spec/type-inference.html).
