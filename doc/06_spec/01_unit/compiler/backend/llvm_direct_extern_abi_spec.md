# Fixed direct extern ABI prerequisite

Authored 2026-10-03; five unexecuted scenarios. Source:
`test/01_unit/compiler/backend/llvm_direct_extern_abi_spec.spl`.

Three fixtures pass real source through frontend, HIR, MIR and LLVM translation.
They require exactly one direct MIR call with matching fixed parameter/result
types and exactly one matching LLVM declaration and call: ParseIRInContext2
has pointer handles, two pointer-to-pointer outputs and i32 status; LLJITLookup
has a pointer result and u64 address output; GetVersion has void result and
three u32 output pointers. Output storage dereferences and native provider
execution are not tested here.

Controls lower an ordinary function and an actual capturing lambda. The former
retains its legacy direct-call operand representation; the latter retains the
existing all-word producer signature with leading capture environment. These
are compiler representation checks, not claims of closure runtime correctness.

The implementation admits only current-module resolved extern declarations
with nonempty fixed parameter lists, no defaults/generics/method/async markers,
32/64-bit integer values, concrete integer/void pointer pointees, and optional
void result. Metadata resets per module. Text adapters, aggregates, unresolved
types and ordinary function values retain their existing behavior. Arity
mismatch on an admitted declaration fails lowering explicitly.

Zero-argument externs remain outside this repair: the backend still conflates
an empty legacy signature with unknown parameter authority. No LLVM-C wrapper,
ORC safe owner or JIT execution is certified by these tests. Native ABI, provider
identity, error ownership and copied-session lifetime checks remain required.
