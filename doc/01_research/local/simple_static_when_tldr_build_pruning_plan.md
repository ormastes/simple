# Simple Static `@when`, Boolable Conditions, TLDR Guard Extraction, and Build-Closure Pruning

**Status:** Proposed language/compiler architecture and implementation plan  
**Date:** 2026-10-06  
**Scope:** Simple language principles, `Boolable`, static condition domains, `@when`, TLDR generation, import/dependency closure, parser/GPU frontend, incremental build/cache, lint/migration, SSpec, and SPipe guidance.

---

## 1. Executive decision

Simple should use **one condition model** for both normal `if` and compile-time `@when`:

```simple
if expr:
    ...

@when(expr):
    ...
@end
```

Both require a `Boolable` condition.

The important difference is **evaluation phase**:

- `if` accepts any expression that is `Boolable` at runtime.
- `@when` accepts only a `Boolable` expression that can be proven and evaluated during the **static dependency scan**, before ordinary import/module resolution.
- Any expression that needs arbitrary CTFE, module execution, file probing, runtime state, or unresolved imports is **not legal** in dependency-affecting `@when`.

Canonical static-domain predicates are compact:

```simple
@when(os.windows):
    ...
@end

@when(os.linux or os.freebsd):
    ...
@end

@when(arch.aarch64 and feature.vulkan):
    ...
@end

@when(profile.critical and not feature.dynload):
    ...
@end
```

### Key semantic rule

`os.windows` is **not string comparison** and is not an arbitrary enum value being treated as truthy.

It is a typed static-domain member predicate:

```text
os.windows : Boolable
```

Conceptually:

```text
selected(os, Os.Windows)
```

but represented internally by stable domain/member IDs, not text.

This keeps the surface language consistent with `if`, avoids stringly typed configuration, remains extremely fast to parse, and is directly suitable for CPU/SIMD/GPU dependency scanning.

---

# 2. Language principle update

Add the following principles to the canonical Simple language design.

## 2.1 Typed semantic domains, not string comparison

When a value belongs to a known semantic domain, Simple should represent it with a typed enum/domain member rather than text.

Avoid:

```simple
@when(os == "windows"):
@when(target_arch == "aarch64"):
@when(backend == "vulkan"):
```

Canonical:

```simple
@when(os.windows):
@when(arch.aarch64):
@when(backend.vulkan):
```

The same principle applies outside `@when` where practical:

```simple
if backend == Backend.Vulkan:
```

is preferable to:

```simple
if backend == "vulkan":
```

Strings remain appropriate for genuinely textual information, unknown external protocol fields, user text, paths, messages, etc.

### Principle

> **Closed or explicitly extensible semantic domains must use typed identities. Do not encode domain identity as text merely because text is easy to parse.**

This removes typo-prone and fail-open behavior such as:

```simple
@when(os == "windwos"):
```

Unknown members must be compile errors, not `false`.

---

## 2.2 One Boolable condition concept

`if`, `while`, guards, and `@when` should share the language's Boolable condition semantics.

However, phase restrictions differ:

| Construct | Condition requirement | Evaluation |
|---|---|---|
| `if` | `Boolable` | runtime or constant-folded |
| `while` | `Boolable` | runtime |
| match/guard condition | `Boolable` | runtime or constant-folded |
| `@when` | **static Boolable** | dependency scan / compile time |
| TLDR guard | **static Boolable** | symbolic, not target-erased |

This is more consistent than creating a second Boolean mini-language with unrelated truth rules.

---

# 3. Should enum itself be Boolable?

## Decision: no implicit truthiness for arbitrary enums

Do **not** make all enum values automatically Boolable.

This would be ambiguous:

```simple
enum State:
    Ready
    Waiting
    Failed

val s = State.Ready

if s:
    ...
```

What does `Ready` mean as truth? What about `Waiting`?

That creates the same hidden semantics Simple is trying to avoid.

Instead, there are two clean cases.

### Case A: an enum/domain member predicate

```simple
os.windows
feature.vulkan
arch.aarch64
```

These are naturally predicates and return static Boolable values.

Conceptually:

```text
os.windows       = selected(os, Os.Windows)
feature.vulkan   = contains(feature, Feature.Vulkan)
```

### Case B: enum explicitly implements Boolable

A user enum may explicitly define Boolable semantics if the language permits it:

```simple
enum Availability:
    Available
    Unavailable

impl Boolable for Availability:
    fn bool(self) -> bool:
        match self:
            case Available: true
            case Unavailable: false
```

Then:

```simple
if availability:
    ...
```

is explicit and type-driven.

For `@when`, that Boolable conversion is usable only when it belongs to the restricted static-evaluable subset.

### Result

This preserves consistency:

```text
condition syntax is shared
truth conversion is typed
arbitrary enum truthiness does not exist
static @when has an additional phase constraint
```

---

# 4. Static domains

A static domain is a typed configuration domain available before ordinary module loading.

Examples:

```text
os
arch
abi
backend
mode
profile
feature
capability
cpu
board
product
```

Each domain has a cardinality.

## 4.1 One-of domains

Exactly one member is selected:

```text
os
arch
abi
backend
mode
profile
```

Examples:

```simple
os.windows
arch.riscv64
backend.llvm
profile.critical
```

`os.windows and os.linux` can therefore be simplified immediately to `false`.

## 4.2 Set domains

Zero or more members can be active:

```text
feature
capability
cpu
```

Examples:

```simple
feature.vulkan
feature.cuda
cpu.avx2
capability.jit
```

`feature.vulkan and feature.cuda` may be valid.

## 4.3 Same grammar, different semantics

The parser does not need different syntax:

```text
DOMAIN '.' MEMBER
```

The static-domain table determines whether the predicate means:

```text
selected(domain, member)
```

or:

```text
contains(domain, member)
```

---

# 5. Extensible `os` and static domains

Simple already has a design for static/complete/dynamic enum closure. Reuse that model rather than inventing a second extension mechanism.

Conceptually:

```simple
enum Os:
    Windows
    Linux
    MacOS
    FreeBSD
    OpenBSD
    NetBSD
    Android
    SimpleOS
    complete:
```

A platform/toolchain/provider may add a sealed member:

```simple
extend Os:
    complete:
        zephyr.Zephyr
```

Then:

```simple
@when(os.zephyr):
    ...
@end
```

may resolve to that stable member if its short name is unique.

### Collision rule

If multiple providers expose the same short member name, the short spelling is ambiguous and must fail.

The implementation may then require a provider-qualified spelling, for example:

```simple
@when(os.zephyr.Zephyr):
```

The exact long spelling can be finalized later. The invariant matters more:

> Source may use a short member name, but semantic identity always contains the stable provider/member ID.

## 5.1 No dynamic enum members in `@when`

A dynamic member cannot influence dependency discovery:

```simple
extend Os:
    dyn:
        plugin.SomeOS
```

must not be usable in:

```simple
@when(os.some_os):
```

because `@when` must resolve before runtime/plugin activation.

Allowed:

```text
static enum member
sealed complete member
```

Rejected:

```text
dyn member
runtime-created member
late plugin registration
```

---

# 6. `@when` is sufficient; do not add another static-if grammar

Simple does not need separate constructs such as:

```text
@cfg
static if
use ... if ...
conditional use
```

Long-term canonical form:

```simple
@when(condition):
    declaration/import/block
@end
```

`@cfg(...)` becomes legacy compatibility syntax.

This keeps:

- grammar small;
- parser logic shared;
- GPU parsing simple;
- TLDR rendering simple;
- diagnostics uniform;
- one static condition representation;
- one migration story.

---

# 7. Static Boolable subset accepted by `@when`

`@when` should use normal Boolable operators, but only a restricted dependency-safe subset.

Canonical grammar:

```text
StaticBoolable :=
      true
    | false
    | StaticPredicate
    | not StaticBoolable
    | StaticBoolable and StaticBoolable
    | StaticBoolable or StaticBoolable
    | '(' StaticBoolable ')'

StaticPredicate :=
      StaticDomain '.' MemberPath
    | approved_builtin_static_predicate
```

Examples:

```simple
@when(os.windows)
@when(os.windows or os.linux)
@when(arch.aarch64 and feature.vulkan)
@when(not feature.dynload)
@when(profile.critical and not capability.jit)
```

## 7.1 What should not be dependency-affecting `@when`

Reject:

```simple
@when(detect_os())
@when(file_exists("/x"))
@when(read_config().feature)
@when(VERSION.major > compute_min_version())
@when(imported_module.static_fn())
```

The reason is architectural, not stylistic.

If import discovery needs normal module resolution or arbitrary CTFE to determine which imports exist, dependency discovery becomes circular:

```text
need dependency
 -> execute condition
 -> need module
 -> need dependency
```

The fast dependency scan must be self-contained.

---

# 8. Static `if` and TLDR

There are two distinct cases.

## 8.1 Structural condition

Canonical source should use `@when` when declarations/imports exist only under a static condition:

```simple
@when(os.windows):
    use win.api.{Handle}
    pub fn native_handle() -> Handle
@end
```

This changes module structure.

## 8.2 Ordinary `if` whose condition is statically Boolable

Inside a body:

```simple
if os.windows:
    return win.create()
else:
    return posix.create()
```

This remains ordinary `if`.

However, the compiler can classify the condition:

```text
classify_static_boolable(expr)
    -> StaticGuard(GuardId)
    -> RuntimeCondition
```

If the body is relevant to the public summary—for example an inline/generic/const/macro body—the references may inherit the static guard.

Thus TLDR metadata can derive:

```text
win.create   -> os.windows
posix.create -> not os.windows
```

and synthesize guarded dependencies.

This provides consistency without changing normal `if` semantics.

---

# 9. Fundamental representation: `GuardId`

Do not retain static conditions as strings.

Every dependency-affecting static condition becomes an interned guard.

```text
type GuardId = u32
```

Reserved:

```text
0 = false
1 = true
```

Atom:

```text
StaticAtom:
    domain_id: u16
    member_id: u32
    polarity: bool
```

General DAG node:

```text
GuardNode:
    op: u8       # atom / not / and / or
    lhs: u32
    rhs: u32
```

For atoms, the node refers to a typed atom table.

No semantic evaluation compares `"windows"` or `"aarch64"`.

---

# 10. Fast path: conjunction representation first

Most source will contain simple nested conditions:

```simple
@when(os.windows):
    @when(feature.vulkan):
```

Do not immediately build a general Boolean tree.

Use a hybrid guard representation:

```text
Guard:
    True
    False
    Conjunction
    ExprDAG
```

`Conjunction` contains:

```text
one_of selections:
    os      -> Windows
    arch    -> AArch64

required set members:
    feature -> Vulkan

negative members:
    feature -> Dynload
```

This makes common nested conditions nearly push/pop operations.

Only promote to `ExprDAG` when needed, primarily when `or` appears.

Example:

```simple
@when(os.windows):
    @when(feature.vulkan):
```

can be represented without a Boolean tree:

```text
{
    os = Windows,
    +feature.Vulkan
}
```

This is important for TLDR/build performance because conjunction-only platform selection should dominate real source.

---

# 11. Hash-cons guards

All general guard nodes should be interned.

Normalize commutative operators:

```text
and(min(a,b), max(a,b))
or(min(a,b), max(a,b))
```

Intern key:

```text
(op, lhs, rhs)
```

Then:

```text
A and B
B and A
```

produce the same `GuardId`.

A small open-addressed hash table is sufficient.

Benefits:

- repeated conditions allocate once;
- declaration/reference records store only `u32`;
- equality is integer equality;
- cache serialization is compact;
- TLDR grouping is cheap;
- GPU output can refer to integer guard records.

---

# 12. Constant-time local simplification

Do not require a SAT solver, BDD, or global Boolean minimizer.

Perform cheap simplification during guard construction.

## 12.1 Identity

```text
A and true   -> A
A and false  -> false
A or false   -> A
A or true    -> true
```

## 12.2 Idempotence

```text
A and A -> A
A or A  -> A
```

## 12.3 Negation

```text
not true  -> false
not false -> true
not not A -> A

A and not A -> false
A or not A  -> true
```

## 12.4 One-of domain contradiction

```text
os.windows and os.linux -> false
arch.x86_64 and arch.aarch64 -> false
```

## 12.5 Absorption

```text
A or (A and B) -> A
A and (A or B) -> A
```

These transformations are local and cheap.

More expensive pretty simplification may be optional when rendering TLDR, but correctness must not depend on it.

---

# 13. One-pass conditional scan

The compiler must not rescan each declaration or import.

Perform one structural pass over source/tokens.

State:

```text
current_guard: GuardId
branch_stack: [BranchFrame]
```

Frame:

```text
BranchFrame:
    parent_guard: GuardId
    taken_guard: GuardId
```

## 13.1 `@when(A)`

```text
current = parent AND A
taken = A
```

## 13.2 `@elif(B)`

Exact branch condition:

```text
current = parent AND NOT(taken) AND B
taken = taken OR B
```

## 13.3 `@else`

```text
current = parent AND NOT(taken)
```

## 13.4 `@end`

```text
current = parent
```

Every declaration/reference discovered while scanning receives the current `GuardId`.

Complexity:

```text
Time:   O(tokens + emitted references)
Memory: O(nesting depth + unique guards)
```

No per-symbol source scan.

---

# 14. Preserve symbolic guards; do not erase them after target evaluation

Current target preprocessing can produce an active source view, but TLDR requires the symbolic reason a declaration/reference exists.

Architecture:

```text
source
  |
  v
static-condition structural scan
  |
  +--> symbolic GuardId attached to regions/decls/refs
  |
  +--> evaluate GuardId(target) for target-active source
```

Do not do:

```text
condition -> true/false -> discard condition
```

because TLDR can no longer reconstruct:

```simple
@when(os.windows)
```

after the condition has been erased.

One symbolic representation should serve:

- target compilation;
- TLDR;
- module dependency closure;
- IDE;
- lint;
- cache invalidation;
- GPU parser;
- diagnostics.

---

# 15. Fast TLDR import generation

TLDR must not copy authored `use` declarations.

Instead it derives imports from reachable public references.

Maintain:

```text
RequiredImportKey:
    owner_module_id
    symbol_id

required_import_guard[key] -> GuardId
```

When a public-summary-relevant reference is emitted:

```text
required_import_guard[key] =
    OR(required_import_guard[key], reference_guard)
```

Example:

```text
Foo referenced under:
    os.windows
    os.windows and arch.aarch64
```

Merged:

```text
os.windows OR (os.windows AND arch.aarch64)
```

Local absorption reduces this to:

```text
os.windows
```

TLDR:

```simple
@when(os.windows):
use foo.{Foo}
@end
```

If any access is unconditional:

```text
true OR anything -> true
```

and TLDR emits:

```simple
use foo.{Foo}
```

---

# 16. TLDR can always render a static guard

This is guaranteed if every dependency-affecting static condition is represented by the closed guard algebra:

```text
atom
not
and
or
true
false
```

Every control-flow path through static conditions is representable.

Example:

```simple
@when(A):
    X
@elif(B):
    Y
@else:
    Z
@end
```

produces:

```text
X = A
Y = !A and B
Z = !A and !B
```

No information is lost.

The TLDR renderer simply serializes the `GuardId` DAG back to canonical `@when(...)`.

---

# 17. Canonical TLDR rendering

Use a deterministic printer.

Precedence:

```text
not
and
or
```

Examples:

```text
Atom(os, Windows)
 -> os.windows

And(os.windows, arch.aarch64)
 -> os.windows and arch.aarch64

Or(os.windows, os.linux)
 -> os.windows or os.linux

And(A, Or(B, C))
 -> A and (B or C)
```

Sort commutative children by stable canonical key, not discovery order.

This produces stable TLDR bytes and stable cache digests.

---

# 18. Eliminate unnecessary `.spl` builds

This feature should be used to reduce the compiler's source closure before parsing/HIR/MIR/codegen.

The target outcome is:

> A `.spl` file that cannot contribute any active required symbol, initializer, macro/CTFE body, re-export, trait/impl/coherence fact, aspect, provider, or other declared semantic effect for the selected configuration must not enter the build closure.

This is broader than simply skipping false `@when` blocks.

---

# 19. Two-stage dependency discovery

Use a cheap structural dependency stage before full frontend work.

## Stage A: cheap module summary scan

For each candidate module, retrieve or construct a compact module dependency summary:

```text
ModuleDependencySummary:
    exported symbols
    guarded import/reference edges
    guarded reexports
    guarded initializer/effect presence
    guarded macro/CTFE dependency refs
    guarded trait/impl/coherence refs
    guarded AOP/provider refs
    summary digest
```

This stage should use:

- source byte scan / structural tokens;
- TLDR/PublicSummary cache when available;
- no HIR/MIR;
- no body parse except explicitly required semantic bodies.

## Stage B: closure expansion

Starting from entry roots:

```text
for each required symbol/effect:
    evaluate guard for target/config
    if false:
        skip edge
    if true:
        add owning module/symbol requirement
```

A module is full-frontend-loaded only when a surviving requirement reaches it.

---

# 20. Symbol-level closure, not file-level import copying

Source:

```simple
use huge.backend.{Cpu, Vulkan, Cuda}

pub fn make() -> Cpu

@when(feature.vulkan):
pub fn vk() -> Vulkan
@end
```

For a build without Vulkan:

```text
required:
    Cpu
not required:
    Vulkan
    Cuda
```

The dependency system should not retain the entire backend module merely because the source authored one broad import if the summary can identify smaller owning modules/symbol partitions.

Where module granularity cannot be reduced, the file may still be needed, but its private bodies and unrelated dependency edges should not be.

This works best together with existing TLDR/PublicSummary work.

---

# 21. Invalid unused imports in TLDR

For TLDR/public-summary generation:

```simple
use broken.does_not_exist.{Unused}
```

must not require resolution if it contributes nothing to the public summary.

Therefore TLDR generation should not:

```text
parse use line
-> resolve every import
-> later discover unused
```

Instead:

```text
public reference graph
-> required symbol
-> resolve owner/import path
```

Rules:

| Source dependency | TLDR behavior |
|---|---|
| private unused import | omit, do not resolve |
| invalid private unused import | omit, do not resolve |
| private-body-only dependency | omit |
| public signature/layout dependency | resolve and emit |
| `export use` | public root, resolve |
| generic/inline/const/macro required body | retain required body/dependency |
| initializer/effect dependency | retain in effect/initialization metadata |
| false static guard | omit before resolution |

Normal executable compilation may still diagnose an invalid authored import according to language policy; TLDR generation itself must not need the invalid private import merely to produce the public projection.

---

# 22. File-level early exclusion

Before reading/parsing a large candidate source file, the dependency index should be able to answer:

```text
does any active required edge need this module/file?
```

If no:

```text
do not:
    read full source
    tokenize full source
    parse
    construct AST
    lower HIR
    run type checking
    lower MIR
    optimize
    codegen
```

Only summary/index metadata is touched.

This is a key startup and build-memory win.

---

# 23. Static false branches must not resolve imports

Example:

```simple
@when(os.windows):
use windows.sdk.*
@end
```

A Linux build must not:

- stat the Windows module candidates;
- parse the Windows module;
- report missing Windows SDK modules;
- include them in snapshot closure;
- include them in dependency invalidation;
- compile them.

The guard must be evaluated before module-path expansion.

This is a stronger and more useful contract than merely preprocessing source after discovery.

---

# 24. Dependency worklist algorithm

Pseudo-design:

```text
queue = entry requirements
seen = map<(symbol/effect, guard/config), state>

while queue not empty:
    req = pop(queue)

    if evaluate(req.guard, selected_static_config) == false:
        continue

    summary = summary_index.lookup(req.owner)

    facts = summary.resolve(req)

    for edge in facts.required_edges:
        G = AND(req.guard, edge.guard)

        if G == false:
            continue

        enqueue(edge.target, G)
```

For one concrete target, `evaluate(G)` is generally O(number of atoms in G) with memoization.

Because guards are interned:

```text
guard_eval_cache[GuardId] -> bool
```

Each unique guard is evaluated once per target/config.

Thus target-specific closure evaluation is approximately:

```text
O(reachable summary edges + unique guards)
```

---

# 25. Multi-target build optimization

For builds targeting multiple configurations, do not rescan source.

Example:

```text
linux-x86_64
windows-x86_64
simpleos-riscv64
```

Share:

- source snapshot;
- structural scan;
- Guard DAG;
- module summaries;
- symbol dependency graph.

Only guard evaluation and target-specific reachable sets differ.

```text
symbolic graph
   + target A -> closure A
   + target B -> closure B
   + target C -> closure C
```

This is especially useful for CI.

---

# 26. GPU parser friendliness

Static-domain grammar is intentionally simple:

```text
@ when ( IDENT . IDENT [operators ...] ) :
```

Tokens needed:

```text
@
when
(
)
.
identifier
and
or
not
:
```

The GPU frontend can:

1. classify bytes / UTF-8;
2. detect directive regions;
3. tokenize static conditions;
4. assign nesting depth;
5. emit condition atoms/operators;
6. prefix-scan block nesting;
7. associate a guard-region ID with declarations/import/reference candidates;
8. leave stable domain/member resolution to a compact indexed table.

No arbitrary CTFE is involved.

---

# 27. SIMD/CPU fast scan

Before running conditional logic:

```text
contains_static_directive(source)
```

Use SIMD/vector byte scanning for `'@'` and likely directive prefixes.

If no static directive and no summary-relevant static `if` exists:

```text
all declarations/ref edges use GuardId TRUE
```

No guard stack or interning table is needed for that file.

This is important because most files should pay near-zero extra cost.

---

# 28. Static `if` extraction in bodies

Do not scan every private body for TLDR.

Only bodies required by the public summary need body-level guarded-reference analysis:

- generic bodies required across modules;
- inline bodies retained cross-module;
- const/CTFE bodies;
- macro bodies/signatures/read sets;
- required trait default/generic bodies;
- AOP advice where body semantics are exposed.

Private ordinary bodies are not TLDR roots.

This prevents TLDR generation from becoming full-program analysis.

---

# 29. Build summary cache

Persist a compact guarded dependency summary keyed by:

```text
source digest
grammar/static-condition schema digest
static-domain universe/seal digest
compiler owner/schema digest
```

Important distinction:

The symbolic summary should **not** normally include the selected OS/arch in its semantic key if the same symbolic graph is valid for all targets.

Instead:

```text
symbolic summary key
    = source + grammar + static-domain universe

target closure result key
    = symbolic summary + selected static configuration
```

This maximizes cross-target reuse.

---

# 30. Static-domain universe and cache invalidation

If an extension changes:

```text
Os
Feature
Backend
...
```

the static-domain universe digest changes.

That invalidates summaries whose member resolution depends on that universe.

Stable built-in IDs should remain fixed.

Sealed complete extension IDs should be derived from stable provider/member identity, not discovery order.

---

# 31. `@cfg` migration

Canonical:

```simple
@when(os.windows):
@when(arch.aarch64):
```

Legacy examples:

```simple
@when(os="windows"):
@cfg(target_arch="aarch64")
@cfg(x86_64)
```

Migration phases:

## Phase 0 — compatibility

Support existing syntax.

Internally normalize immediately to typed static atoms.

## Phase 1 — lint/advice

Suggest:

```text
@when(os="windows")
 -> @when(os.windows)

@cfg(target_arch="aarch64")
 -> @when(arch.aarch64)
```

## Phase 2 — warning

String-valued closed-domain static comparisons warn.

`@cfg` warns as legacy syntax.

## Phase 3 — high-reliability profile

String-valued static-domain conditions become errors.

## Phase 4 — possible removal

Only after repository migration and bootstrap parity.

---

# 32. Diagnostics

Unknown static member:

```text
error E-STATIC-MEMBER:
`windwos` is not a member of static domain `os`

  @when(os.windwos)
           ^^^^^^^

did you mean:
  os.windows
```

Wrong domain:

```text
error E-STATIC-DOMAIN:
`windows` belongs to `os`, not `cpu`
```

Dynamic member:

```text
error E-STATIC-DYN:
dynamic enum member cannot participate in dependency-time @when
```

Non-static Boolable:

```text
error E-WHEN-NONSTATIC:
condition is Boolable but not available during dependency discovery
```

String form:

```text
warning W-STATIC-STRING:
closed static domain `os` should use typed member syntax

replace:
  @when(os="windows")
with:
  @when(os.windows)
```

Impossible condition:

```text
warning W-STATIC-IMPOSSIBLE:
condition can never be true:
  os.windows and os.linux
```

---

# 33. Interaction with high-reliability mode

Recommended policy:

Normal mode:

- legacy string static comparison: warning;
- unknown member: error;
- fail-open fallback: forbidden.

High-reliability mode:

- legacy static-domain string syntax: error;
- ambiguous short extension member: error;
- dynamic member in static guard: error;
- non-static Boolable in `@when`: error;
- impossible guard may be error where it makes public API unreachable.

The compiler must never silently map malformed static conditions to `false`.

---

# 34. Public summary contract changes

Extend `PublicSummaryV1` or its successor with guarded facts.

Conceptually:

```text
PublicSummaryEntry:
    symbol_id
    ...
    guard_id

PublicSummaryReference:
    from_symbol_id
    to_symbol_id
    kind
    guard_id

StaticGuardTable:
    domains
    atoms
    nodes
```

The public summary should contain the minimal guard DAG required by its entries/references.

Do not duplicate condition text on each entry.

---

# 35. TLDR generation algorithm

```text
input:
    PublicSummary
    guarded public references

1. Determine public roots.
2. Traverse only summary-semantic dependencies.
3. For every external symbol reference:
       G = path_guard AND reference_guard
       import_guard[module,symbol] |= G
4. Drop G=false.
5. Group symbols by module + canonical GuardId.
6. Emit unconditional groups directly.
7. Emit guarded groups under @when(render(G)).
8. Emit public declarations under their own guards.
9. Keep deterministic ordering.
```

Example output:

```simple
use common.ui.{Window}

@when(os.windows):
use win.api.{Handle, Hwnd}
@end

pub struct App:
    window: Window

@when(os.windows):
pub fn native_handle(app: App) -> Hwnd
@end
```

---

# 36. Avoid repeated `@when` blocks when cheap to group

Given:

```text
module win.api:
    Handle -> os.windows
    Hwnd   -> os.windows
```

emit:

```simple
@when(os.windows):
use win.api.{Handle, Hwnd}
@end
```

not two blocks.

If declarations share the same guard and preserving declaration order permits grouping, the renderer may group them. However, grouping is presentation optimization; correctness and stable ordering come first.

---

# 37. Build-pruning architecture

Target pipeline:

```text
source snapshot
   |
   v
cheap structural/static scan or cached summary
   |
   v
symbolic guarded dependency graph
   |
   +--> target/config guard evaluation
   |
   v
minimal active symbol/effect closure
   |
   v
load/parse only required modules/bodies
   |
   v
HIR/MIR/codegen only for reachable active program
```

This replaces the less efficient shape:

```text
discover broad imports
 -> read many .spl
 -> parse many .spl
 -> later discover target/private/unused paths are unnecessary
```

---

# 38. Important exceptions to pruning

A module/file cannot be removed merely because no ordinary function/type reference is seen.

The summary must account for semantic roots such as:

- module initializer;
- exported/re-exported symbol;
- macro;
- CTFE dependency;
- compile-time generated declaration;
- trait/impl/coherence contribution;
- extension declaration;
- AOP selector/advice;
- linker/provider registration;
- required FFI/link metadata;
- explicit side-effect import if Simple supports one;
- reflection metadata where semantically declared;
- test registration in test mode.

The optimization must be semantic, not a naive unused-import text pass.

---

# 39. Side-effect imports should be explicit

To make aggressive closure pruning safe, imports whose purpose is module initialization/registration should be explicit rather than relying on an apparently unused normal `use`.

A possible future form can be selected separately, e.g. a dedicated initialization import or manifest declaration.

Until then, the summary/index must conservatively retain modules with known initialization effects.

Long-term language principle:

> **An unused symbol import must not secretly be the only way to request a side effect.**

This makes dependency pruning reliable.

---

# 40. Performance targets

The implementation should be judged by explicit budgets.

Suggested targets:

## No-condition file

Additional static-guard overhead:

```text
<= 1 lightweight SIMD/byte pre-scan
no guard allocations
no condition token arrays
GuardId = TRUE constant
```

## Conditional file

Structural condition extraction:

```text
O(source bytes/tokens)
one pass
no source copy if possible
bounded nesting stack
hash-consed guards
```

## TLDR

```text
O(public summary entries + public reference edges + unique guards)
```

No full source reparse.

## Closure

```text
O(reachable guarded dependency edges + unique evaluated guards)
```

No traversal of inactive dependency subtrees.

## Memory

Per declaration/reference:

```text
GuardId: 4 bytes
```

plus shared guard table.

---

# 41. Performance counters

Add counters so regressions are visible:

```text
static_scan_files
static_scan_bytes
static_scan_fastpath_files
guard_atoms
guard_nodes
guard_intern_hits
guard_intern_misses
guard_eval_hits
guard_eval_misses

summary_files_loaded
source_files_avoided
source_bytes_avoided
modules_pruned_false_guard
modules_pruned_unreferenced
private_body_parses_avoided

tldr_imports_authored
tldr_imports_emitted
tldr_unused_imports_removed
tldr_false_guard_imports_removed
```

Build reports should show both work done and work avoided.

---

# 42. SSpec / test matrix

## Static Boolable

- `os.windows`
- `arch.aarch64`
- `feature.vulkan`
- `not`, `and`, `or`, parentheses
- One-domain contradiction
- set-domain conjunction
- explicit Boolable enum where static-evaluable
- non-static Boolable rejection

## Branches

- `@when`
- `@when/@else`
- `@when/@elif/@else`
- nested branches
- many siblings
- deep nesting limit
- malformed/unclosed block
- line/span preservation

## Domain errors

- typo
- wrong domain
- ambiguous extension
- dynamic extension
- unsupported member
- stale static-domain seal

## TLDR

- unconditional public reference
- conditional public reference
- same reference under multiple guards
- unconditional + conditional merge
- impossible guard removed
- invalid unused private import omitted
- invalid required public import fails
- guarded re-export
- guarded trait/impl/coherence
- guarded generic/inline body refs

## Build pruning

- false OS import never resolved
- false OS module never stat/read
- unused private module not full-parsed
- initializer module retained
- macro/CTFE dependency retained
- trait/coherence provider retained
- entry closure result parity with broad build
- multiple targets share symbolic summary

## GPU/CPU parity

Given the same source:

```text
same StaticAtom IDs
same canonical Guard DAG
same declaration GuardId
same dependency edges
same TLDR bytes
```

---

# 43. Fuzz/property tests

Useful invariants:

```text
render(parse(G)) == canonical(G)

evaluate(G,target)
 == evaluate(parse(render(G)),target)

guard_of_each_branch is mutually exclusive for one @when/elif/else chain

OR(all branch guards) == parent guard when final else exists

target-pruned public summary
 == public summary generated from symbolic guards then evaluated for target

broad compile observable output
 == pruned compile observable output
```

For one-of static domains:

```text
selected(os,a) AND selected(os,b) == false, a != b
```

---

# 44. Incremental invalidation

When a private body changes but:

- public summary is unchanged;
- guarded dependency edges are unchanged;
- required semantic body refs are unchanged;

dependents should not rebuild.

When a guard changes:

```simple
@when(os.windows)
```

to:

```simple
@when(os.windows or os.linux)
```

only affected dependency/target closures should invalidate.

The symbolic guard digest is part of the summary semantic identity.

---

# 45. SPipe updates

Update SPipe guidance so agents preserve these rules.

Suggested SDN policy:

```sdn
language:
  static_condition:
    canonical_construct: when
    condition_type: Boolable
    dependency_phase: static_only

    semantic_domain:
      string_compare: forbidden
      unknown_member: error
      dynamic_member: forbidden
      complete_member: allowed

    syntax:
      preferred:
        - os.windows
        - arch.aarch64
        - feature.vulkan
      legacy:
        - cfg
        - string_domain_compare

    tldr:
      import_source: guarded_symbol_graph
      copy_authored_imports: false
      resolve_unused_private_imports: false

    build:
      false_guard_import_resolution: forbidden
      inactive_module_full_parse: forbidden
      symbolic_guard_cache: required
```

Agent guidance:

1. Do not introduce new `@cfg`.
2. Do not introduce string comparison for closed target/config domains.
3. Use `@when(domain.member)` for declaration/import existence.
4. Preserve `GuardId` when moving/refactoring guarded declarations.
5. Do not "fix" a pruned import by broadening the closure.
6. Side-effect dependencies must be explicit and retained by semantic metadata.
7. TLDR imports are synthesized from references, never copied mechanically from source.
8. Any optimization claim must report source/module work actually avoided.

---

# 46. Documentation updates

Recommended repository documents:

## Language principles

Add or extend a canonical document under:

```text
doc/04_architecture/language/
or the existing canonical language-principle owner
```

Sections:

- typed semantic domains;
- no string identity for closed domains;
- one Boolable condition model;
- static phase restriction.

## Requirements

Add requirements for:

```text
typed static domains
@when static Boolable
fail-closed member resolution
symbolic GuardId preservation
TLDR guarded import synthesis
inactive dependency non-resolution
minimal build closure
```

## Design

Update:

```text
parser/frontend conditional design
module resolver
compiler semantic cache/PublicSummary
TLDR renderer
GPU parser architecture
incremental dependency/cache architecture
```

## Guides

Update:

```text
syntax quick reference
module/import guide
target/platform guide
performance/build guide
```

## Migration

Create a guide covering:

```text
@cfg -> @when
os="windows" -> os.windows
target_arch="..." -> arch....
legacy alias normalization
```

---

# 47. Implementation phases

## Phase 0 — contracts and measurements

- Freeze `StaticDomainId`, `StaticMemberId`, `GuardId`.
- Add baseline counters for current source reads/parses/modules.
- Record build/TLDR baseline on representative entry closures.

No syntax behavior change.

## Phase 1 — typed static-domain registry

- Built-in `os`, `arch`, `feature`, `profile`, etc.
- Stable IDs.
- One/set domain metadata.
- Complete-extension sealing.
- Fail-closed unknown-member diagnostics.

Keep legacy syntax as input normalization.

## Phase 2 — Boolable/static classifier

- Share condition typing rules with `if`.
- Implement `classify_static_boolable`.
- `@when` requires static classification.
- Domain-member predicates produce static Boolable.

## Phase 3 — GuardId structural scanner

- One-pass directive scan.
- Conjunction fast path.
- DAG fallback for `or`.
- Hash-cons.
- cheap simplifier.
- preserve spans/line mapping.

## Phase 4 — frontend integration

- Attach `GuardId` to declarations/import/reference candidates.
- Produce target-active view by evaluating guards.
- Stop erasing symbolic condition provenance.

## Phase 5 — TLDR/PublicSummary guards

- Add guarded declaration/reference records.
- Synthesize imports from guarded public references.
- Do not copy raw imports.
- Canonical `@when` renderer.

## Phase 6 — resolver pruning

- Evaluate guards before import path expansion.
- False guarded imports perform zero module resolution.
- Build closure expands from required symbols/effects.

## Phase 7 — full `.spl` work avoidance

- Cache module dependency summaries.
- Avoid source read/full parse for modules excluded by active closure.
- Avoid private body parse where public summary is sufficient.
- Report files/bytes/modules avoided.

## Phase 8 — GPU/SIMD path

- GPU/static condition token classifier.
- parallel region/nesting association.
- parity with scalar GuardId graph.
- SIMD pre-scan fast path on CPU.

## Phase 9 — migration warnings/autofix

- warn string domain condition;
- warn `@cfg`;
- autofix deterministic cases;
- high-reliability mode errors.

## Phase 10 — bootstrap cleanup

- remove duplicate Rust-seed/self-host conditional logic only after parity;
- one shared static-condition contract;
- cold/full-scan and incremental paths must consume the same symbolic guard semantics.

---

# 48. Acceptance criteria

The feature is complete only when all of the following hold.

### Language

- `if` and `@when` share Boolable semantics.
- `@when` rejects non-static Boolable expressions.
- arbitrary enums are not implicitly truthy.
- domain/member predicates are typed, not text comparisons.
- unknown static members fail closed.

### TLDR

- every dependency-affecting static path has an exact renderable `@when`;
- imports are synthesized from guarded references;
- private unused imports disappear;
- false guarded imports disappear;
- output is deterministic.

### Build

- false guarded modules are not resolved;
- pruned modules are not full-parsed/compiled;
- semantic side-effect roots remain correct;
- output parity holds against broad closure builds.

### Performance

- no-condition files take the near-zero fast path;
- conditional extraction is linear;
- no per-symbol source rescans;
- no SAT/BDD dependency;
- cached summaries avoid unnecessary `.spl` reads/parses;
- counters prove reductions on representative builds.

### Parser

- scalar/SIMD/GPU static-condition facts are identical;
- one-pass parsing remains possible.

---

# 49. Recommended final syntax

```simple
# single-choice domain
@when(os.windows):
    ...
@end

# OR
@when(os.linux or os.freebsd):
    ...
@end

# combined domains
@when(arch.aarch64 and feature.vulkan):
    ...
@end

# negative feature
@when(profile.critical and not feature.dynload):
    ...
@end
```

Ordinary condition:

```simple
if availability:
    ...
```

where `availability` implements Boolable.

Static domain predicate:

```simple
if os.windows:
    ...
```

is also legal if static-domain predicates are exposed in ordinary expressions; it may be constant-folded.

Structural existence:

```simple
@when(os.windows):
    ...
@end
```

is the explicit declaration/import selection mechanism.

---

# 50. Final architecture

```text
                          SOURCE
                            |
              +-------------+-------------+
              |                           |
              v                           v
       fast byte/SIMD scan        ordinary tokenizer
              |
       static conditions?
        /             \
      no               yes
      |                 |
 GuardId.TRUE      structural static scan
                        |
                 typed StaticAtoms
                        |
               interned GuardId DAG
                        |
            +-----------+-----------+
            |                       |
            v                       v
     target evaluation       symbolic summary graph
            |                       |
      active source                 |
            |                       +--> TLDR @when
            |                       |
            |                       +--> guarded imports
            |                       |
            |                       +--> cache/invalidation
            |                       |
            +-----------+-----------+
                        |
                dependency closure
                        |
            false guards removed first
                        |
             required symbols/effects
                        |
                minimal modules/bodies
                        |
                 parse/HIR/MIR/codegen
```

The critical design outcome is:

> **Simple should know why a dependency exists before paying the cost of compiling it.**

`Boolable` provides one consistent condition model.  
Typed static domains eliminate fragile string comparison.  
`GuardId` preserves exact static conditions cheaply.  
TLDR renders those guards back to `@when`.  
The resolver evaluates them before import expansion.  
The build system then avoids reading/parsing/compiling unnecessary `.spl` files.

This should be treated as both a language-safety improvement and a compiler startup/build-performance feature.
