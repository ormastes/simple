# Fixed direct extern ABI prerequisite

Authored 2026-10-03; thirteen unexecuted scenarios. Source:
`test/01_unit/compiler/backend/llvm_direct_extern_abi_spec.spl`.

Four fixtures pass real source through frontend, HIR, MIR and LLVM translation.
They require exactly one direct MIR call with matching fixed parameter/result
types and exactly one matching LLVM declaration and call: ParseIRInContext2
has pointer handles, two pointer-to-pointer outputs and i32 status; LLJITLookup
has a pointer result and u64 address output; GetVersion has void result and
three u32 output pointers; ContextCreate has a fixed zero-argument pointer result.
Output storage dereferences and native provider
execution are not tested here.

Controls lower an ordinary function and an actual capturing lambda. The former
retains its legacy direct-call operand representation; the latter retains the
existing all-word producer signature with leading capture environment. These
are compiler representation checks, not claims of closure runtime correctness.

The implementation admits only current-module resolved extern declarations
with fixed parameter lists, no defaults/generics/method/async markers,
32/64-bit integer values, concrete integer/void pointer pointees, and optional
void result. Metadata resets per module. Text adapters, aggregates, unresolved
types and ordinary function values retain their existing behavior. Arity
mismatch on an admitted declaration records a fatal error and returns a typed
rejected temporary without emitting an extern call; a malformed-HIR fixture
checks that behavior. An actual captured lambda calling an extern verifies that
the fresh same-module lowerer retains declaration authority. Bootstrap fresh
lowerers seed their maps from their own module declarations.
Declaration seeding precedes runtime constant/array initializers; an actual
frontend module passed through the flat bootstrap lowering checks a zero-argument
extern inside an array initializer. Three further fixtures read the canonical
raw declaration owner and lower its zero-argument, i32/out-pointer and LLJIT
creation signatures, rather than duplicating those declarations in the fixture.

The additive params_known flag defaults false. Only admitted resolved externs
set it true. A zero-argument call remains distinct from unknown legacy empty
arity through the return-type repair copy and LLVM external declaration. A
separate test checks backend and serialized signature identities; no owned JSON
MIR deserializer was found, so no serialization roundtrip is claimed.
No LLVM-C wrapper,
ORC safe owner or JIT execution is certified by these tests. Native ABI, provider
identity, error ownership and copied-session lifetime checks remain required.
