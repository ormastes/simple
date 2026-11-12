# Robust Semantic Absence: Choosing an Input Type

**Canonical language guide** for public APIs in robust code. This is the
normative text of §2 of the design
[Simple Robust Types, State-Dependent Fields, and Layer Contracts](../../05_design/language/robust_types/robust_types_layer_contracts_2026-11-12.md)
(2026-11-12). Compiler enforcement status lives in that design (§11); this
guide states the rules authors follow today.

The central rule: **a later layer must receive a type that proves every
property it requires.** Safe code does not reach that by assigning `nil`,
guessing a default, repeatedly unwrapping `Option<T>`, or asserting that a
value probably exists.

## Public surface rules

- **`ROB-OPT-001`:** public function, method, constructor, callback and generated setter input must not expose `Option<T>`.
- **`ROB-OPT-002`:** exported attribute/property and generated getter must not expose `Option<T>`.
- **`ROB-OPT-003`:** robust-mode ordinary safe code ultimately rejects raw optional types in return values, locals, nested collection/tuple/function types, aliases and `T?` sugar too. Public inputs/attributes are the first priority, not the only eventual targets.
- `Option<T>`, `T?`, `List<Option<T>>`, type aliases, generic specialization, re-exports and inferred public accessors **all count**. A nominal domain type that happens to contain a valid state enum is not automatically an `Option` exemption.
- The only planned raw-optional exceptions are **explicitly reviewed HAL/interpreter declaration capabilities**. Neither a path name nor `--engine=interpreter` grants a capability. A public adapter should translate the boundary value into a semantic domain result as early as possible.
- Do not promote genuinely private fields into public findings merely because their containing class is exported.

Lint status: `ROB-OPT-001`/`ROB-OPT-002` are emitted by the
`robust_option_surface` lint rule at **warning** severity (never deny);
`NIL-UNSAFE-001` is the existing `nil_outside_unsafe` rule. Both are
compatibility warnings until the rule-by-rule error gate of the design's
phase E.

## Required distinctions

| Term | Meaning | Robust-safe usage |
|---|---|---|
| `None` | The enum variant of a typed legacy optional | `case None:` only when matching a proven `Option<T>` at an allowed compatibility/boundary site; **not** a new raw absence literal |
| `nil` | Raw nil/null literal | Rejected in safe source including assignment, return, comparison and `case nil:`; only explicit `unsafe:` / `danger:` — **except** as the value of the unit type `Nil` (see § Unit type) |
| `Nil` | The unit type ("succeeded, nothing to return"); its single value is `nil` | `Result<Nil, E>` / `Ok(nil)`, `-> Nil` / `return nil`; never `Nil?` and never absence |
| `NotInit<T>` | Reserved storage before the first valid `T` is constructed | Private/pool/stack backing only, with compiler proof before reading; not a substitutable `T` |
| `Err(E)` / meaningful enum | Failure, cancellation, disconnected, unavailable, etc. | Preferred for explicit domain semantics |
| `T = default` | Valid and documented contract default | Allowed only after checking default constructor, invariants, callers, behavior and ABI |

## Unit type

`Nil` is the unit type and `nil` is its only value (Ruby/Crystal spelling):

```simple
fn save(path: text) -> Result<Nil, text>:
    if path == "":
        return Err("empty path")
    Ok(nil)
```

- `Nil` is unit, never absence. Absence is `T?` / `None`. `Nil?` and
  `Option<Nil>` are rejected.
- In safe code `nil` is legal only where a `Nil` value is expected (`Ok(nil)`
  for `Result<Nil, E>`, `return nil` for `-> Nil`). Any other `nil` is the raw
  null and stays `unsafe:`-only (`NIL-UNSAFE-001`).
- `()` is accepted as the same type; new code prefers `Nil`.
- Rationale and cross-language comparison:
  `doc/01_research/language/types/unit_type_nil_spelling_2026-11-12.md`.

Do not rewrite `nil` tokens into `None` tokens mechanically: their current representation and source meaning differ. Do not rewrite `Option<T>` into `NotInit<T>`; initialization progress and domain absence are different concepts.

## Choosing an input type

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

## Migration checklist

Before changing an existing public declaration:

1. **Find all users:** call sites, derived/generated constructors/getters, interfaces, aliases, macros and re-exported entry points.
2. **Identify semantics:** does absence mean a valid default, another operation, a transient state, a failure, an FFI null or merely not-yet-initialized storage?
3. **Choose one design:** concrete `T`; explicit valid default; payload enum; split API; `Result`; state-specific layer type; private `NotInit<T>`; or reviewed HAL/interpreter adapter.
4. **Prove each transition:** exact field initialization, variant exhaustiveness, stable ownership, mutation and async invalidation, ABI and cache revision.
5. **Offer and review multiple fixes:** all alternatives with caller impact, not a single generic `unwrap()` or automatic `None` replacement.
6. **Verify behavior:** native/interpreter parity, SSpec tests, no-panic/invalid-state rejection, memory layout and hot-path CPU before enabling Deny.

## Historical optional/nil examples (compatibility-only)

Older guides still show raw optional and `nil` shapes. They document
**compatibility behaviour of the current engines**, not robust-API guidance,
and must not be copied into a new public declaration:

- `doc/07_guide/language/type_system.md` § Union Types: `type OptionalInt = i64 | nil` and `fn divide(...) -> i64 | nil: return nil` — legacy union-nil spelling; a robust API returns `Result<i64, DivideError>` (Rule F).
- `doc/07_guide/language/error_handling.md` § Option: `fn find_user(id: i64) -> Option<User>: return nil` — `nil` in a safe return is `NIL-UNSAFE-001`; a robust API returns a domain enum or `Result` (Rules F, G).
- `doc/07_guide/language/type_system.md` § Optional Chaining Types: `val user: User? = get_user()` — local `T?` sugar is tolerated today; it is `ROB-OPT-003` territory once robust mode rejects raw optionals in locals.

Rule G above is the only sanctioned `None` pattern, and only at an audited
compatibility/boundary site.
