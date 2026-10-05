# Optional Boolean enum payload boxed as integer

Status: source and native-object cause confirmed; focused owner repair awaiting validation.

The native `Some`/`Ok`/`Err` payload helper classified `BOOL` with integers and
emitted `BoxInt`. A retained LLVM object from the seven-case optional-Boolean
probe calls `rt_value_int` in `returned_boolean` before `rt_enum_new`. Consequently
true becomes tagged integer 8 instead of tagged Boolean 11, and the correct
`rt_value_as_bool` decoder returns false. The probe ran five passing cases and
two failures (direct and returned true); it is not qualification evidence.

Route Boolean payloads through the existing shared scalar-boxing owner, which
emits `rt_value_bool`. Keep integer/U64 boxing and the strict runtime decoder
unchanged. Five targeted MIR tests cover direct/returned Some, Ok, Err and
unchanged integer Some, including the constructor's actual boxing-result operand.
They are authored but UNRUN at this checkpoint. Earlier four default/HIR tests
passed; those do not validate this newly found boxing defect.

The separate core-C representation probe did not execute: clang-cl failed with
out-of-memory while compiling its main stub. The initial core-C probe also
showed that `--runtime-path` does not override the checkout-first core-C source
policy; runtime provenance must bind the actual C compiler source path, not only
the requested archive/fallback path. No source-selection policy was changed.

Evidence: runtime/windows-restart-20261004/native-method-defaults-native-proof3
(`bool/run.log`, `bool/object.asm`, `representation/compile.log`). Preserve the
three scoped native attempts; no fourth broad probe was launched.
