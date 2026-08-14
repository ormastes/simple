# Provider query pointer signature was not Pure-Simple exportable

Status: fixed in this change.

The initial host bridge typed provider buffers as `const uint8_t*` and
`uint8_t*`. Simple `@export("C")` functions currently expose scalar ABI types
but no raw-pointer type, so a Pure Simple provider would export `(i64, i64)`.
Calling that function through a pointer-parameter function type is C/Rust
incompatible-function-type undefined behavior even where both values occupy
the same machine register.

The v1 provider ABI now defines buffer locations as nonzero `uint64` address
scalars. Providers convert those addresses only through the canonical runtime
raw-byte helpers. Lengths remain explicit and bounded. The host C oracle and
the Pure Simple provider use the same scalar signature.

Regression evidence:

- exact Rust function-pointer tests;
- host shared-library provider gate;
- Pure Simple source provider using only scalar exported parameters.
