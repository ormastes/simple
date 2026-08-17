# Text Split Semantics — Feature Expert

## Contract

`text.split(separator, limit)` returns at most `limit` parts when the limit is
positive, preserving the unsplit tail. Empty separators split by Unicode
scalar value, not byte. A missing/nonpositive limit keeps the unbounded form.

## Owner boundaries

- Pure-Simple MIR tags the receiver and separator as text but transports the
  limit as raw numeric `i64` to `rt_string_split_limit`.
- Pure-Simple interpreter and both Rust interpreter dispatchers consume the
  second argument numerically. Do not repair one execution mode while leaving
  another divergent.

## Regression contract

Use `nested_string_split_spec.spl` for literal and variable limits plus
multibyte delimiters. The Rust dispatcher unit test independently covers the
exact bounded result and Unicode empty-separator adjacency.
