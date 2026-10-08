# Native method Result enum-subject recovery

This integration check compiles and executes
`test/fixtures/compiler/native_result_method_enum_subject/main.spl` as a
standalone native program. The fixture declares another enum with bare `Ok`
and `Err` variants, then matches the `Result` returned by an imported
instance method and an imported static method. It verifies both values at
runtime, so an ambiguous or incorrectly selected enum owner fails the check.

Run `scripts/check/check-native-result-method-enum-subject.shs` with the
self-hosted Simple compiler selected through `SIMPLE_BIN` or `bin/simple`.
This fixture and checker have not yet been compiled or executed on the
qualified compiler generation; they are regression inputs awaiting that run.
