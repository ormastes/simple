# Feature request: const-generic dimension parameters (`Embedding<D>` where D is a number)

- **Id:** search_const_generic_dimension_2026-06-15
- **Priority:** P2 (TOP-PRIORITY language-capture item for search-custom-types)
- **Filed:** 2026-06-15
- **Area:** type system / generics

## Motivation
The search/ANN type barrier wants `Embedding<D>` where `D` is the vector
*dimension* — a compile-time number — so that `dot`/`l2` between two embeddings
of mismatched dimension is a type error, not a runtime length check.

## What Simple supports today
Only *type* parameters: `List<T>`, `HandleArena<T>`, `PostingList<Id>`. A
search of `src/lib/` found NO const-generic (value/number) generic parameter
anywhere. There is also no evidence of a trait/where bound on generic params
(sorted-merge `<` on a generic `Id` only works because the interpreter is
dynamically typed; see PostingList<Id> below).

## What failed / forced workaround
`Embedding<D>` cannot make `D` a dimension. Two concrete problems:
1. **No const-generics:** `D` cannot be `768` / a number; it can only be a type.
2. **Unused type param risk:** a struct `Embedding<D>` that never stores a
   `D`-typed field is at best a phantom tag.

Workaround applied in `src/lib/common/search/types.spl`:
- `D` kept as a *phantom* type tag (carries no dimension information).
- Real dimension stored as an `i64` field `dim`, checked at runtime.
- `dot`/`l2` cannot enforce equal-dimension at compile time.

## Requested capability
1. Const-generic params: `struct Embedding<const D: i64>` so `D` is a number and
   `Embedding<768>` is distinct from `Embedding<512>`.
2. (Related) bounded generics / `where` clauses so `PostingList<Id where Id: Ord>`
   can statically guarantee the `<` used by sorted-merge intersect/union, instead
   of relying on dynamic dispatch in the interpreter.

## Impact if unfixed
ANN/embedding code carries runtime dimension checks and cannot prevent
mismatched-dimension dot products at compile time. Acceptable for Phase-1
(fixed-point i64 path proven by spec), but blocks a fully type-safe vector API.
