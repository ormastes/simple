# Self-hosted compiler lacks accessor (get_/is_/set_) and `alias Trait = field` forwarding

Date: 2026-10-26. Status: open. Owner: compiler 20.hir / 50.mir lane.

## Symptom
Programs relying on `obj.x` -> `get_x()`/`is_x()`, `obj.x = v` -> `set_x(v)`, and
`alias Trait = field` work on the Rust seed but not when compiled by the
self-hosted `src/compiler`.

## Seed vs self-hosted
- Seed: getter/setter forwarding at `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:616`,
  `interpreter/node_exec.rs:863`, `hir/lower/expr/access.rs:743`; plus `alias Trait = field`.
- Self-hosted: no get_/is_/set_ fallback found in `src/compiler/20.hir` or `50.mir`
  (grep for "get_"/"set_"/"is_" literals: only unrelated `mir_json.spl:622`).
- `src/compiler/20.hir/hir_forward_lowering.spl:28-29` lowers only Phase 2
  (`alias fn/me NAME = FIELD.METHOD`); phases 1/3/4 reported by
  `unrepresented_forward_forms`, deliberately not lowered (layering).
- `src/app/desugar/forwarding.spl` (`desugar_forwarding`, called at
  `src/app/desugar/mod.spl:227`) is an offline text desugar. No call site found in
  `src/compiler/80.driver`; only `src/app/cli` desugar command surfaces and the
  mdsoc port `85.mdsoc/feature/desugaring/app/ports.spl` reference it. So it does
  not run in the normal self-hosted compile path (not fully traced).
- Parser: `alias` is a recognised binding keyword (`10.frontend/core/parser_stmts.spl:826`);
  I did not find a dedicated `alias Trait = field` parse node. Unconfirmed.

## Spec (red -> green)
`test/01_unit/language/accessor_forwarding/accessor_forwarding_spec.spl`
(related seed bugs: seed_setter_forwarding_silent_noop, seed_hir_getter_setter_forwarding_dejit,
seed_trait_alias_forwarding_unsupported, all 2026-10-26).

## Size estimate
~400-700 LOC: HIR field-expr/assign lowering fallback (resolve missing field ->
get_/is_/set_ method, hard error when no setter) ~150-250 LOC in 20.hir (+ type
check hook in 30.types/35.semantics); `alias Trait = field` parse + HIR
expansion over abstract trait methods ~200-300 LOC; MIR needs little (lowers to
ordinary calls). Plus spec wiring.

## Known unsupported
`obj.x += 1` on a forwarded name is unsupported (seed too); must error clearly.

## Progress 2026-10-27: PR1 (read forwarding) implemented
- `_Expressions/accessor_forwarding.spl` (`lower_accessor_read`) hooked at the end of the `ExprKind.Field` arm in `expression_core.spl`, after the real-field lookup. Order: real field, `get_x`, `is_x`, `x()`; owner must be known (>=0) else today's untyped Field is kept.
- Undefined-field error: opt-in `SIMPLE_STRICT_FIELD_FORWARDING=1`, read once (cached); default off keeps old behaviour.
- Spec `test/01_unit/compiler/hir/accessor_getter_forwarding_spec.spl` (REQ-SELFHOST-ACCESSOR-001): red 2/6 (reads not forwarded, strict flag no-op), green 6/6.
- Gaps: bootstrap flat path (module_declarations_bootstrap.spl:561) not mirrored; forwarded call is untyped (no return type); census of strict-mode hits in src/compiler not run; setter/alias PR2-4 untouched.
