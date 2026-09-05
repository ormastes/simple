# Option f64 match-return native ABI bug

Status: known red; not fixed by the config-parser correction.

`test/fixtures/compiler/option_f64_match_return_native_red.spl` reproduces a
native lowering defect in a value-position `match Option[f64] -> f64`. The
generated function drops the incoming f64 default and returns an encoded enum
payload instead of an unboxed f64 value. Direct native f64 equality lowers
correctly; the parser fixture and its decimal inputs are not the cause.

`Option[f64].unwrap_or(default)` reaches the same lowering defect because the
core method is implemented as a value-returning match. It is therefore not a
workaround for this bug; callers using it remain native-red until the shared
MIR match-result lowering is corrected.

The compiler fix belongs in MIR match-result typing/payload extraction. When it
lands, promote the fixture into the native system-test manifest and require exit
status 0 for both the `Some` and `nil` arms.
