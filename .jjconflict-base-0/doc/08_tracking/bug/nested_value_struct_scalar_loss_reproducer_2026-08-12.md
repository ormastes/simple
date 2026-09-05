# Nested value-struct scalar loss: minimal reproducer audit

## Status

Narrowed; the proposed minimal compiler shape does not reproduce the loss.
The larger SOSIX positioned-dispatch failure remains open and must not be
attributed to constructor, call, or return evaluation without a richer
compiler-only reproducer.

## Proposed failure shape

`Outer` contains `Inner(token: u64, bytes: [u8])`. A function copies the byte
array, mutates its first byte, computes token `12` inside a branch, constructs
a new `Inner`, constructs a new `Outer`, and returns it. The oracle checks both
the mutated bytes and token. An adjacent control returns `Inner` directly and
computes token `13`.

Executable probes:

- `test/fixtures/compiler/nested_struct_scalar_reconstruction_repro.spl`
- `test/01_unit/compiler/interpreter/nested_struct_scalar_reconstruction_spec.spl`

## Evidence

The isolated fixture completed under interpreter mode with:

```text
nested-rebuild bytes=[20, 0] token=12
```

The exact shape traverses constructor evaluation, value-struct parameter
copying, branch-local scalar assignment, nested constructor reconstruction,
tail-expression return copying, and caller field access. Both fields survived.
Therefore none of those evaluator boundaries is falsified by this minimal
shape, and changing them would be speculative.

The installed `bin/release/x86_64-unknown-linux-gnu/simple` currently identifies
itself as a Rust bootstrap seed, so this is diagnostic evidence rather than an
admitted self-hosted release verdict. The admitted staged pure-Simple bootstrap
accepts `native-build` for the fixture without diagnostics but currently emits
no requested output artifact, so it does not supply a runtime verdict.

## Remaining unblock condition

Reduce the larger failing transition while retaining one additional ownership
layer at a time (registry owner, registry arrays, dispatch result, then kernel
state) until the first failing shape is found. Only then claim and change the
pure-Simple constructor/call/return owner. The focused probes above must remain
green as adjacent regressions.
