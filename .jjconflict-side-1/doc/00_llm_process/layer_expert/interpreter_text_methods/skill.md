# Interpreter Text Methods — Layer Expert

## Boundary rule

Text-method dispatch must preserve each argument's semantic type. Blanket text
coercion is invalid for mixed-signature methods such as
`split(separator: text, limit: i64)`.

## Cross-engine parity

When changing a text method, inspect the pure-Simple interpreter, pure-Simple
MIR/native lowering, and every live Rust interpreter dispatcher. Exact tests
must include a nonliteral argument; adjacent tests must include Unicode and an
edge separator or limit.

## Admission

Rust unit tests decide Rust dispatch only. Interpreter/native language closure
requires the same focused SSpec on a provenance-admitted pure-Simple Stage 4
CLI; seeds and stale deployed binaries are diagnostic, not closure evidence.
