<!-- codex-research -->
# Feature options: canonical HIR callable identity

## Option A — Module identity table (recommended)

Add a stable `CallableIdentity` value and retain a
`Dict<SymbolId, CallableIdentity>` on each `HirModule`. Calls keep their current
module-local `SymbolId` transport; semantic consumers resolve it through the
module table. The stable identity frames canonical logical module, lexical
owner, declaration kind/name, normalized resolved signature, generic arity,
and dispatch convention.

- Pros: avoids widening every call-expression payload; isolates compatibility;
  gives semantic gates and MIR one canonical source; codec/hash can version the
  table once.
- Cons: every imported/resolved callable must populate the table; consumers
  need module context; true overload support still requires signature-aware
  symbol registries.
- Effort: L, approximately 12–18 model/generator/lowering/spec files before
  overload-registry completion.

## Option B — Identity on every resolved call payload

Add an optional stable identity to direct, method, and static HIR call variants.
Resolution fills it after selecting a declaration; every transform retains or
deliberately replaces it.

- Pros: each call is self-describing; downstream validation and MIR do not need
  a module-side lookup; unresolved identity is visible at the use site.
- Cons: widens several enum variants and at least dozens of constructors,
  visitors, codecs, substitutions, and backend matches; higher regression and
  memory cost per call edge.
- Effort: XL, approximately 30–50 files including generated artifacts.

## Option C — Source path/owner/name identity

Retain the current scanner-style identity based on source path, lexical owner,
and short callable name.

- Pros: smallest change; works without semantic resolution.
- Cons: not overload-safe or relocation-stable; aliases, reexports, duplicate
  names, and imported calls can false-match or be missed; cannot prove the
  requested contextual safety property.
- Effort: S, approximately 3–6 files, but not suitable for production
  E-APACK008 enforcement.
