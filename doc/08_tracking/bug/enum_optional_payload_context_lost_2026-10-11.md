# MIR enum payload check rejects direct `Some(i64)` for `i64?`

Status: OPEN compiler bug. The Item 5/6 branch uses a typed-local workaround in `DimExpr.named_range`; this does not repair direct optional construction generally.

## Reproduction

- Admitted pure-Simple Stage 2 binary SHA-256: `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`.
- Fixture `test/fixtures/compiler/enum_optional_payload_direct_repro.spl` declares `Named(name: text, lo: i64?, hi: i64?)` and passes `Some(lo), Some(hi)` directly. The tested identical source under `build/mini_builds/item56_dimexpr_option_probe.spl` exited 1 in 0.216 s with `enum construction ... DimExprKind.Named: payload type mismatch at 1` at the first `Some(lo)` argument.
- Control fixture `test/fixtures/compiler/enum_optional_payload_typed_control.spl` binds `Some(lo)` and `Some(hi)` to explicit `i64?` locals before construction. The tested identical source under `build/mini_builds/item56_dimexpr_option_local_probe.spl` compiled to SMF, exit 0 in 0.239 s.
- Both used `SIMPLE_LIB=src <admitted-stage2> compile <fixture> --format=smf --output <output>`. The only semantic difference is the local type binding.

## Scope and next repair

`src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl` checks declared enum slots after lowering. A direct built-in `Some(...)` reaches the optional slot without type evidence accepted by `enum_payload_local_compatible`; a typed local supplies it. This is a diagnostic inference from the paired fixture and source, not a proven root cause in HIR transport. Preserve nominal/container validation when repairing the checker: a raw i64 carrier must not authorize an arbitrary Optional. Add a positive direct-constructor case and a negative wrong-inner-type case, then rerun both fixtures and the affected compiler closure.
