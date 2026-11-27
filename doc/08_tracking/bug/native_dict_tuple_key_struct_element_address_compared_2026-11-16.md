# Native Dict with a tuple key holding a struct compares the struct by ADDRESS

- **Date:** 2026-11-16
- **Status:** OPEN (pre-existing; recorded, not fixed, by `work/native-struct-keyed-dict-generic-20261115`)
- **Severity:** P2 (silent miss; live in the compiler's trait solver cache)
- **Lanes:** native cranelift + llvm (pure-Simple Stage 2). Seed interpreter is correct.

## Symptom

A tuple key whose element is a struct misses on an equal key built elsewhere:
seed interpreter prints `v 3`, native prints `v -1` (review probe of the
struct-keyed dict branch, 2026-11-16).

## Root cause

A native tuple is a headerless `rt_alloc` block, and so is each struct element.
The runtime hashes and compares the tuple word by address. The struct-key
canonicalization added on the branch (`canonical_struct_dict_key_v1`,
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`) handles only a key
local that is itself a struct, or a struct held in an Optional local. The
`E-MIR-STRUCT-DICT-KEY` refusal does not look inside tuple keys either, so a
struct element passes through silently.

## Live sites

`src/compiler/25.traits/trait_solver.spl:186/189`:
`cache: Dict<(HirType, HirSymbol), bool>` and
`active: Dict<(HirType, HirSymbol), bool>`. Both elements are multi-field
structs. Value-keying single-word structs inside tuples would NOT cover these
sites. Natively the cache misses (extra solving work), and `active` may miss a
pending proof, which risks re-entering a cycle that the seed detects.

## Why it is not fixed here

Value-keying requires a tuple-key encoding (hash and equality over element
values, then rebuild on `keys()` and iteration) for multi-field structs. That
is a runtime key-model change, not a MIR key-site rewrite. The narrower
"single-word struct inside a tuple" variant would leave both live sites
broken. Pitfalls table row: `doc/07_guide/language/dict_native_pitfalls.md`
(`K` = tuple).

## Next step

Choose one: (a) give tuple keys a value encoding in the runtime, with
element-wise hash and equality over canonical words; or (b) refuse a struct
element in a tuple key at compile time, then re-key `TraitSolver.cache` and
`active` by a text or integer digest of `(HirType, HirSymbol)`.
