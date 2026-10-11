# Array return records with function fields lack a complete semantic snapshot

Status: source-level limitation recorded; native regression not run. The current compiler owner repair has only static validation.

`result_err_field_type_key` supplies the provider semantic field-signature snapshot used for record ownership validation. It currently has no Function arm. A record containing a function-valued field therefore has an empty snapshot, even when the independent function-field signature ownership registry can encode that field.

Returning an array of such records must reject the missing snapshot rather than trust byte-layout equality or a provider-local Named ID. Byte offsets cannot distinguish two same-sized fields with different semantic types. This conservative rejection can expose previously admitted code; it is an unresolved compiler capability, not a supported execution claim.

The focused compile-rejection fixture is `test/fixtures/compiler/native_array_return_function_field_unsupported/main.spl`, with its diagnostic contract in `expected_error.txt`. No native job was launched for this fixture. Once the snapshot supports complete function signatures, change this fixture to require compilation and actual prefix/callback assertions.

A valid zero-field record has the explicit complete snapshot `fields[]`, not an empty string. `native_array_return_record_owner` contains a positive zero-field record array iteration regression so missing metadata cannot be conflated with an empty declaration.
