# C2 recursive nominal declaration source packet

Status: SOURCE ONLY; all executable scenarios, generated Lean elaboration and
kernel checks UNRUN. This is one implementation subitem of the selected full
C1–C7 scope in `doc/03_plan/generic_formal_verification_hardening_plan.md`.
Recursive fixed arrays, unions, general aggregate control flow, enum elimination,
calls and mutation remain OPEN. C1/C6/C7 refinement and trust are separate.

## Ownership and interface

Base: `af10a7acd2ffa5fe9e487cf3c5bd15fcc4aa5c2a` (prepared PR3974).
Private branch: `work/formal-c2-recursive-declarations-20261020`.
Private checkout: `/home/yoon/dev/simple-formal-c2-recursive-declarations-20261020`.
Author: recursive_declarations; merge owner: root; independent review required.
Parent owns `lean_nominal_body.spl`; this packet must not modify it.
No build, compiler, tests, Lean execution, seed, commit, push or admission changes.
Maximum three source review/fix cycles, retaining previous packet bytes.

Owned source: `src/plugins/backend_lean/lean_type_declarations.spl` and only
declaration imports/emission in both retained `lean_backend.spl` entrypoints.
Owned tests: recursive declaration specs, and the obsolete cycle-refusal scenario
in the existing declaration spec. Manuals mirror executable spec paths.

Retain `LeanTypeContext` and every `LeanTypeDeclaration` field unchanged.
Add `LeanTypeDeclarationGroup(declarations, recursive)` and mandatory `groups`
to `LeanTypeExportPlan`; retain its flattened `declarations` compatibility view.
Repository constructor/read search found only the producer in
`lean_type_declarations.spl`, the two `export_types` consumers and tests reading
the flattened view. No default empty groups or ad-hoc fallback is permitted.
The sole producer builds both views in the same loop.

Export each nonrecursive singleton exactly as before. Export recursive strongly
connected components in `mutual ... end`, using inductives for both enum and
struct members. Structs use a single `mk` constructor and explicit match-based
field definitions after `end`, at the existing qualified projection names.
Metadata follows the completed group, outside `mutual`. The nominal body owner
continues using `context.names[symbol] + ".mk"` and quoted field names.
The owner-local exported `lean_recursive_struct_projections` helper returns
projection source lines; it accepts a validated declaration and its context.

## Selected acceptance obligations

- REQ-C2-REC-001: real public full/generated APIs on both owners export direct
  self-recursive enums and mutually recursive structs/enums.
- REQ-C2-REC-002: nominal construction and field projection retain exact
  constructor/projection identity; metadata, qualified same-short names, field
  order, discriminants and symbol IDs remain distinct.
- REQ-C2-REC-003: positive Slice/Array, Tuple/Prod and Result/Except nesting;
  refuse recursive fixed Array/Vector occurrences precisely.
- REQ-C2-REC-004: exact existing acyclic ordering/output; deterministic grouped
  order independent of insertion; malformed/kind/unknown/identity failures,
  FuncPtr negative positions, unions and reserved members refuse atomically.
- REQ-C2-REC-005: no axioms/sorry; actual generated Lean checking is a separate
  UNRUN gate, never inferred from source-string assertions.

These obligations derive from selected C2; they do not replace the full C2
contract or claim that source review proves production compilation.

## Algorithm and resource bounds

Build indexed dependency and reverse adjacency once from validated plans.
Use iterative Kosaraju traversals, explicit node/cursor stacks, then a component
dependency graph and integer min-heap keyed by the first name-sorted member.
No recursive graph calls, dependency-path expansion or global caches.
Every graph edge is visited a bounded number of times. Parallel component edges
are counted and decremented equally; deduplication is unnecessary.
Graph workspace is O(V+E); ordering is O((V+E) log V), plus source text output
and pre-existing table/member validation. Existing name-overlap and dependency
deduplication costs remain separately visible. No measured time/RSS claim.

Recursive-wrapper checking walks original field/payload type trees once per
recursive declaration, with component membership keyed by symbol ID. Primitive
and function/reference refusal remains the exact existing mapper policy.
Fixed-array wrappers are rejected only when an occurrence of a member of the
same recursive component is beneath them. Independent acyclic Vector fields
retain their exact prior representation.

## Lean 4.30 source basis

Read-only toolchain source root:
`/home/yoon/dev/robust-tdd-20261014/toolchains/lean-4.30.0-linux_aarch64/src/lean`.
Pin consulted files in the external dependency manifest.

- `Lean/Elab/MutualInductive.lean`: common mutual elaborator; `withInductiveLocalDecls`
  registers each type with both short and full declaration name before elaborating
  constructors. All emitted types have zero parameters and live in Type.
- `Lean/Meta/Basic.lean` / `Lean/LocalContext.lean` / `Lean/ResolveName.lean`:
  auxiliary declaration full-name registration and matching; the resolver's
  mutual Foo/Bar example includes qualified and `_root_` names.
- `Lean/Declaration.lean`: nested inductive documentation explicitly names
  `Array T`, `List T` and `T × T`.
- `Init/Prelude.lean`: Prod has positive fields; Except's error/ok constructors
  take their parameters positively; Array is a List wrapper.
- `Lean/Data/Trie.lean`: actual `Trie.node` constructor nests recursion in Array.
  `Lean/Compiler/IR/Basic.lean`: actual mutual Alt/FnBody declarations, nested
  Array Alt, and qualified match-based `FnBody.body` projection provide the
  constructor/group/projection syntax precedent.
- `Lean/Elab/MutualInductive.lean:addAuxRecs` and
  `Lean/Meta/Constructions/BRecOn.lean`: nested recursion creates numbered
  `rec_N`, `below_N` and `brecOn_N` auxiliaries. Recursive members reserve these
  numeric families before emission; acyclic output is unaffected.
- `Lean/Meta/SizeOf.lean:169–188,360,514–527`: automatic recursive SizeOf
  generation creates `_sizeOf_N`, `_sizeOf_N_eq` and `_sizeOf_inst` in nominal
  namespaces. Independent cycle1 review found these omitted from revision1.
  Revision2 reserves them for recursive fields and variants and adds public
  full/generated and builder-atomicity controls plus nearby valid-name controls.
- `Init/Data/Vector/Basic.lean`: Vector contains `toArray` and the dependent
  `size_toArray` proof. This packet does not claim its nested recursive
  elaboration; a precise refusal retains that open requirement.
- Existing backend builder emits named inductive constructors; existing nominal
  bodies require qualified `.mk`/field functions. Explicit constructor matching
  preserves those APIs without depending on recursive structure eta rules.

Source investigation establishes the implementation contract, not accepted
generated output. Full-name mutual references and projection terms require
actual generated-module Lean checking before any runtime/verification PASS.
