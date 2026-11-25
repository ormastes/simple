# Native ExistsCheck uses its presence boolean as a struct payload

- **ID:** native_exists_check_struct_payload_becomes_bool_2026-07-25
- **Status:** OPEN
- **Severity:** high for native `optional_struct.?.field` expressions
- **Lane:** native-build / Cranelift

## Reproduction

On hosted AArch64, compile an imported class getter returning `Evidence?`, bind
the result, then evaluate `evidence.?.marker`.

## Evidence

The refreshed Stage 3 caller correctly moves the class receiver into `x0`
before both zero-argument getters. After the optional getter returns, the
generated code calls `rt_is_some(evidence)`, zero-extends that `i1`, masks it
as though it were a tagged pointer, and performs the `marker` field load from
the resulting address. It never emits or calls `rt_unwrap_or_self`.

The resulting exit 132 (`field access on nil receiver`) is therefore downstream
of the getter and independent of receiver marshalling.

## Expected correction

Preserve the ExistsCheck payload local through its some/none merge and attach
the inner struct provenance to that merged local. Do not substitute the
`rt_is_some` condition local for the expression result. Add a focused native
fixture for `optional_struct.?.field` before closing this issue.

## Triage note — 2026-11-25 (release/1.0.0 fleet pass)

Still **OPEN**; not reclassified. What changed since filing:

- The codegen pipeline this bug was observed in has been substantially
  reworked: `ExistsCheck` no longer appears anywhere under
  `src/compiler_rust/compiler/src/codegen/` — it is desugared during HIR
  lowering (`hir/lower/expr/control.rs` and siblings), and the surrounding
  optional-payload handling has had multiple later fixes (e.g.
  `b4a07b71d00` "fix Dict.get text ExistsCheck decode"). The exact
  2026-07-25 instruction shape (rt_is_some boolean masked as a tagged
  pointer for the field load) can neither be confirmed present nor absent
  by inspection alone.
- Confirming or closing this needs the lane it was filed on: hosted
  native-build (the original evidence is AArch64 disassembly). That lane is
  not exercisable from this Windows verification host, and the doc's own
  closing condition — "add a focused native fixture for
  `optional_struct.?.field`" — still has no dedicated fixture in
  `test/fixtures/compiler/` (the nearest,
  `native_trait_optional_struct_return.spl`, covers trait returns, not the
  `.?.field` payload-preservation shape).

Next step for whoever picks this up: re-run the original reproduction on a
hosted native-build lane at current HEAD; if it passes, add the focused
fixture and close; if it fails, the HIR-level desugar is the place to look,
not the per-backend codegen this doc originally blamed.
