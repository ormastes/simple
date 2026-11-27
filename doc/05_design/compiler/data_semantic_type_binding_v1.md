# Semantic owner adapter for exact schema type binding

Accepted plan: [section3.2](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md).
Baseline: `53419f623a540659087f2ad8e925349dcbbbf7a4`.
Status: adapter and integration tests authored; semantic dependency integration,
independent final review and runtime qualification pending.
<!-- codex-architecture -->

## One authority and layer direction

`compiler.hir.data_type_binding_v1` prepares an existing HirLowering context
before bodies: freeze explicit semantic policy, copy `module.nogc_strict`, run
the existing import/sibling registration passes, then declare module symbols.
It verifies required declarations were registered and returns errors rather
than accepting an ambient bootstrap shortcut's empty declaration pass.

`data_bind_type_identity_v1(Type)` invokes the existing `lower_type` owner.
Aliases, generic substitution/defaults/cycles and symbol lookup belong to that
owner. `compiler.hir.data_semantic_type_identity_v1` then projects a fully
bound HirType using the SAME lowering context, including retained module
surfaces and materialized terminal-origin facts. SymbolTable alone is not a
sufficient imported-rename/re-export authority.

The adapter calls the existing provider/consumer origin operations and
`hir_payload_terminal_identity`; the latter becomes public without changing its
implementation. It preserves existing canonical module compatibility rules.
Imported enum/trait registration restores the original declaration name; a
same-provider alias-spelling collision is tested through actual parser/import
metadata rather than repaired by an invented alias table. Missing owner,
stale symbol/index, inconsistent terminal kind or unresolved diagnostic is an
error. Process-local SymbolId never appears in the transported descriptor.

Layer direction is HIR -> pointer-free common descriptor. Common does not
import HIR/frontend/types. V3 consumes the validated exact descriptor through
the canonical schema reducer; frozen V1/V2 paths, argument meanings, outputs
and digests remain unchanged. No synthetic nominal identifier hides a rich
descriptor, and no short/long digest substitutes for exact type comparison.

## Source and SDN parity

Source fields pass their parsed Type directly. SDN type text uses
`data_parser_type_text_v1`: one byte-bounded complete line is parsed by the
existing checked reference parser as a single type-alias carrier. The helper
requires exactly that carrier, no other declarations or module-policy facts,
then binds its target Type in the caller's already-authorized module context.
SDN cannot select an owner by supplying an unchecked owner string. The W1b
consumer retains original SPL/SDN provenance and produces two-location schema
conflicts; this adapter returns type-owner errors, not synthetic provenance.

The checked helper refuses unsupported parser-provider/original-coordinate
conditions; it does not silently fall back or invent a separate type grammar.
Multiline type spellings and unbound/unresolved semantic constructors are
explicitly unsupported in this version, never partially admitted.

## Exact projection and bounds

The complete common wire preserves integer/float widths and signedness,
nominal module/name/kind plus recursive arguments, tuple/array/slice/dict,
Optional/Result, ordered HIR unions, raw/reference mutability and all four
ownership wrappers. Function parameters/result and declared effects are
included; effects are sorted/deduplicated with recursive Throws types. Unknown
or custom effects without a bound identity are refused. Infer/Error/unbound
TypeParam/Projection and tensor/layer shapes are refused by this version.

Depth32, 1024 aggregate visited nodes, 256 children and 65536 UTF-8 bytes are
enforced during projection. The node budget is a functional remaining-budget
argument, avoiding shared mutable counters or a new lowering-state field.
Child/effect accumulation is bounded before append, and the common bounded
packer checks complete framed cost before parent assembly. No parsing,
resolution or comparison is added to attribute-access hot paths. Cold binding
uses retained declarations only; it adds no filesystem scan, cache authority,
environment read, process call or runtime TypeId registry.

## Dependency and evidence boundary

This integration requires two actual owner repairs: generic-alias parser/core
bridge preservation (SolMIR) and HIR nominal generic defaults/arity normalization
(SolNativeABI). The alias semantic owner already exists; the flat bridge's
previous `type_params: []` must not be hidden with a schema-specific parser.
Likewise the adapter must not normalize omitted nominal arguments itself.
Actual parsed generic/default acceptance cases are authored and remain pending
until those reviewed owner changes are integrated. Bound-shape transport alone
is not the accepted plan's final admitting W1 binder.

Sixteen authored integration cases cover source/SDN nested generics, actual
and owner-provided aliases/defaults, nominal defaults/arity, cycles, owner/ID
stability, import rename/re-export/homonym collisions, strict-policy reset,
qualifiers/effects, unresolved metadata, malformed text and semantic traversal
bounds. The companion manual is authored, not generated execution evidence.
No test, coverage, latency/RSS, doc-maintenance or compiler/MCP smoke PASS is
claimed. The final admitting pipeline requires the exact admitted producer and
the reviewed dependency identities plus actual source/SDN consumer execution.
