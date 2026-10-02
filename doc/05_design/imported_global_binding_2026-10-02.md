# Imported global binding repair contract

Status: implementation candidate and failing fixtures; execution pending. Separate from
PR 2172's enum/global-receiver repairs. Root review owner: bootstrap coordinator.

The imported `[text]` constant reproducer reaches MIR with an imported symbol
but no global value/storage binding. It emits undefined-variable and then an
I64 unsupported-iterable cascade. Provider source must own initialization and
storage; consumers must never clone the initializer or define another slot.

## Required behavior

| ID | Contract | Native fixture observation |
|---|---|---|
| GB-1 | Imported literal/initialized arrays retain declared type and contents | Two expected text elements; no I64 iterable fallback |
| GB-2 | All consumers access one mutable provider slot | Writer increments; independent reader observes the change |
| GB-3 | Provider initializer dependencies retain owner scope and execute once | Derived value is 42; initialization counter remains one |
| GB-4 | Alias names preserve physical declaration identity | Two providers' `VALUE` symbols remain 7 and 9 |
| GB-5 | Cross-module global initializers execute after their dependencies | Dependent provider observes 43, not zero/default storage |
| GB-6 | One storage definition per declaration | Provider defines; consumers reference; no duplicate static definitions |
| GB-7 | Missing/ambiguous owners and initialization cycles fail closed | Actionable diagnostic; no zero placeholder accepted as success |

Primary positive fixture: `test/fixtures/compiler/imported_globals/main.spl`.
Tests must inspect emitted definition/reference identities as well as compile
and execute. An exit-zero interpreter run cannot validate native storage.

## Binding ownership

At HIR import registration retain terminal owner, original declaration name,
declared type and mutability; the lexical import alias remains a lookup key.
Reuse existing imported type relocation and re-export resolution. Do not infer
identity from a short name or copy a provider-local numeric SymbolId.

Build one per-consumer demand index from imported Const symbols, then consult
only demanded provider owners. Register only requested globals. The index is
module-local, discarded on reset, and contains no parser/global frontend roots.
Target complexity is O(consumer HIR nodes + provider names + declarations in demanded providers),
with O(1) lookup on each global read/write. No source scans on expression paths.

The provider determines storage representation and link identity. Consumers use
the same representation after named-type relocation. Initializer expressions
and their SymbolIds stay in the provider's symbol table. Consumers hold a
reference/declaration, never another initializer. Read, assignment, compound
assignment and aggregate mutation must all use that single identity.

## Backend boundary under review

The candidate uses an explicit trailing imported/declaration flag on
MirStatic (default false), with external declarations in LLVM/Cranelift and
undefined data symbols in native object backends. A declaration must never
allocate bytes or receive zero initialization. Static serialization/schema
receipts carry the flag. VHDL rejects imported runtime globals explicitly.

An accessor ABI is a possible implementation fallback, but would need explicit
read/write/address semantics and initialization guards. Do not silently replace
global storage with calls merely to avoid the representation work.

Reuse one link-name helper for provider definition and consumer reference.
Preserve the full visibility lattice. Exported folded constants require an
addressable provider slot or a separately proven pure constant projection;
do not create a private consumer copy of mutable or initialized storage.

## Initializer ordering

Existing startup discovery sorts module initializer names and explicitly does
not guarantee dependency order. The candidate therefore adds a guarded provider
initializer with states unstarted/active/complete and a stable forwarding entry
independent of the bootstrap module index. Imported reads, writes and addresses
call this entry before touching storage. A complete initializer returns
immediately; a recursively active initializer reports a cycle through rt_panic.
Referenced imported functions register their provider initializer too; direct
calls and function-value reads invoke the guard before crossing the owner
boundary. Same-provider function calls do not recurse into their own guard.
Dependencies reached through initializer function calls are covered too, without
trying to approximate their behavior from syntactic import order.
Initialization remains serialized by the existing pre-main startup contract;
the guard is not an atomic concurrent plugin-initialization API.
`test/fixtures/compiler/imported_globals_cycle/main.spl` must diagnose the cycle.

## Integration and verification

The duplicate-static owner supplies commit 829d89e72a, which finalizes provisional
and runtime static entries by numeric symbol ID within one module. Keep that
single-definition fix distinct from cross-module declaration identity.

Before native acceptance, check HIR alias/type retention, owner-qualified MIR
read/write bindings, backend definition counts, and provider initializer
dependencies. Then compile and execute the fixture once with an updated
self-hosted producer, private cache, admitted memory cap and retained receipts.
No Rust seed fallback; no claimed PASS from source-only tests.

Current executable verification status: UNRUN. The declaration-identity and
storage-binding unit specs are under `test/unit/compiler/hir/`; positive native
coverage and the negative cycle fixture are under `test/fixtures/compiler/`.
The ordinary and flat bootstrap MIR paths share provider binding logic. Flat
static metadata retains the external flag with explicit reset and transient
root promotion; aggregate LLVM emits the owning definition only.

Current limits are explicit: imported declarations whose provider HIR still
has an unresolved storage type produce a diagnostic. Cranelift's existing data
SFFI combines declaration and definition, so imported data is rejected until a
declaration-only boundary is available. VHDL rejects runtime imported storage.
LLVM and native object backends represent external data without allocating a
second slot. These backend changes are source-reviewed candidates, not runtime
qualification evidence.
