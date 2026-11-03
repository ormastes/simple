# Native dictionary array value erasure

Status: OPEN. Source workaround authored; native validation UNRUN.

The Phase2 producer built from 916be6c20617637e2cccf3d18c23669470ab8ffe
(compiler SHA256 2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33)
failed both Cranelift and LLVM trait lifecycle fixture compilations. Both
reported unresolved `contains` and two unsupported for-in collections of MIR
type I64 in `reverse_reference_facts.spl`. Neither fixture executed.

Evidence: windows-restart-20261004/qualification-916be-memory-trait1/
{cranelift,llvm}/trait_lifecycle/compile.log and its parent results.json.
The diagnostic source location 36:72 points at the dictionary declaration;
logs also warn its array value type is erased to Any. Three direct indexed
dictionary values feed one contains call and two loops. This is the suspected
type propagation defect, not proof that every dictionary array read fails.

Workaround: explicitly bind those reads to `[text]` locals, matching the
existing typed lookup pattern in the same owner. No ownership, ordering,
deduplication, lifetime, or cache completeness gates change. The background
compiler fix must preserve dictionary value type through indexed expressions
without requiring source annotations; it is not implemented by this patch.

Regression: source_alias_array_lookup.spl checks real phase/module alias
deduplication, merged ordering, rollback, and absent identity. The existing
incomplete_family.spl checks lifetime publication independently. Next bounded
diagnostic validation should compile/run both with each actual backend using
the current producer and private source overlay/cache; preserve all failed
receipts. Do not restart ongoing bootstrap phases for this workaround.

**Revalidated 2026-11-02: still plausible because OPEN. Source workaround authored; native validation UNRUN; no merged fix commit with a passing regression is cited in this doc.**

**2026-11-03 (sonB): deferred, concrete blocker.** HIR Index typing already propagates Dict value types (`expression_core.spl` ~960-975 `case HirTypeKind.Dict(_, value)`, since 2026-08-21), so the erasure happens before that: the module-level `{text: [text]}` brace type or the module-var Var expr has no `type_` when `d[k]` is lowered. Need an HIR dump of `reverse_reference_facts.spl:36-44` on stage3 to see which; workaround ([text] locals) retained.

**2026-11-03: fix-implemented-verification-pending.** Root cause: the parser's
brace dictionary type branch (`src/compiler/10.frontend/core/parser.spl` ~1386-1398)
discarded the parsed key/value tags and returned bare `TYPE_DICT`, so `{text: [text]}`
lowered to `Dict<Any, Any>` and `d[k]` produced an Any/I64 value. Fixed by
978e606e4a6 (`dict_type_register(key_tag, value_tag)`), which landed AFTER the
failing producer 916be6c2061 (not an ancestor). Regression: 
`test/01_unit/compiler/parser/dictionary_brace_type_identity_spec.spl` and
`test/04_smoke/native_dictionary_array_direct.spl`. Repro: build a producer at or
after 978e606e4a6, native-build `test/04_smoke/native_dictionary_array_direct.spl`
with cranelift and llvm; expect no unresolved `contains` and no I64 for-in.
The `[text]` local workaround in reverse_reference_facts.spl may then be removed.
