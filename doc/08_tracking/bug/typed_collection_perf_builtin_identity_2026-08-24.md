# Typed collection diagnostics lack a built-in method identity

## Status

Open compiler/lint integration blocker. Source-audited on 2026-08-24; runtime
verification was not available in this tranche.

## Observed code

- `HirTypeKind.Array` and `Slice` carry no `SymbolId`.
- `TypeChecker.get_type_symbol` and `try_instance_method` therefore cannot
  produce an `InstanceMethod` identity for their built-in methods.
- Primitive trait synthetic keys do not cover Array or Slice.
- MIR lowering explicitly treats Array `contains`, `find`, and `rfind` as
  unresolved and prevents them from falling into text search lowering.
- `rt_array_contains` is declared to LLVM but has no matching generic runtime
  implementation. The current pure-Simple self-hosted native MIR path
  deliberately fails loudly instead of returning a plausible wrong result.
  Rust/interpreter lanes and a specialized numeric helper are separate
  capabilities and do not satisfy that generic native contract.
- The initial `HirPerfFacts` unit fixture uses synthetic method symbols. No
  production registry builder can honestly bind `Array.contains` today.

## Consequence

A symbol-keyed typed COLL002 warning cannot be wired to normal compiler or lint
execution yet. Treating receiver spelling plus method text as a resolved call
would reintroduce the syntactic ambiguity the typed design is intended to
remove. Treating a caller-supplied receipt or raw numeric ID as authoritative
would make diagnostic severity forgeable and revision-unsafe.

## Required repair

1. Give compiler-owned built-in collection callables collision-free identities
   in the same per-compilation symbol universe used by `MethodResolution`, or
   add an equally explicit typed built-in-call identity. Do not require a
   globally stable numeric `SymbolId`.
2. Re-intern deterministic stable keys for each compilation/reset/cache
   boundary and bind any ephemeral numeric IDs to that exact universe.
3. Resolve only proven built-in receiver kinds and exact arities, plus
   signature compatibility wherever typed evidence is already available;
   otherwise defer or fail closed. Ordinary named/user methods retain normal
   instance/trait/UFCS precedence.
4. Implement or explicitly capability-gate the corresponding runtime/MIR
   operation. Do not mark an unsupported operation as production metadata.
5. Build an immutable collection-operation registry after resolution from the
   exact module symbols and signatures. Bind it to the compilation revision;
   do not persist raw `i64` IDs across revisions.
6. Make missing, duplicate, mismatched, or unsupported rows a visible
   `AnalysisIncomplete`/registry error. They must never become typed warnings,
   errors, or transformation authority.

## Acceptance evidence

- Positive Array and Slice built-in identity witnesses.
- Same-named user/trait/UFCS methods remain distinct.
- Wrong receiver, arity, signature, revision, and duplicate rows fail closed.
- HIR codec/cache round trips preserve the ordinary resolved identity.
- Interpreter and native behavior agree for supported element/equality kinds.
- Typed COLL002 consumes the production registry without parsing or source
  name inference; Allow/Warn/Deny policy is applied once by its policy owner.
- Unsupported equality kinds fail with a precise compiler diagnostic rather
  than linking an absent runtime symbol or silently using text semantics.
