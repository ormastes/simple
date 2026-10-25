# Struct inequality never dispatches to an existing __eq__ method

Status: observed RED; source repair and regressions authored; GREEN pending.

The one-module fixture defines ModuloRecord.__eq__ as equality modulo10.
The admitted pure-Simple producer645e62a8 accepts its ordinary equality method
and the `same` function, but MIR fails specifically at `a != b` in `different`
(line13). The native build exits1 with quiescent=1 and peak RSS3275500KiB.
The source dispatcher maps Eq but omits NotEq from its dunder table.

The repair maps both operators to __eq__, calls it once, and applies MIR logical
Not to the result only for inequality. Nil-presence handling remains earlier
in the dispatcher. Three authored MIR scenarios verify the call/result dataflow,
ordinary equality, nil bypass and fail-closed behavior for a missing method.
The native fixture checks a custom relation, so field or pointer inequality
cannot satisfy the expected result. Native GREEN requires a rebuilt producer
containing the source repair; the old binary cannot exercise its replacement.

Commands, original source snapshot and raw failure are retained under
`build/native_probe/items247-struct-inequality/` (`compile-red.log`,
`process-red.env`). The standalone fixture is
`test/fixtures/compiler/native_struct_inequality/main.spl` and the compiler
unit source is `test/01_unit/compiler/50.mir/struct_inequality_lowering_spec.spl`.
This does not implement automatic structural equality for every language type.
