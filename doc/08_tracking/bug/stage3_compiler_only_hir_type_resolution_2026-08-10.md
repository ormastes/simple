# Stage3 compiler-only self-host HIR type resolution failure

## Status

Open. This blocks rebuilding the pure-Simple compiler-only Stage3 needed by the
current ARM64 QEMU producer lane.

## Reproduction

The deployed admitted Stage3 was used to native-build
`src/app/cli/bootstrap_main.spl` with the admitted `core-c-bootstrap` runtime,
one thread, `SIMPLE_NO_STUB_FALLBACK=1`, `--mode dynload`, and a preserved cache.
The final bounded attempt log is:

`build/mini_builds/qemu-port-stage3-attempt3.log`

## Result

After roughly 25 minutes of frontend work, the in-process builder exits before
object production with a large family of HIR type-resolution errors. Repeated
examples include `MirSignature`, `SymbolId`, `AggregateKind`, `MirAsmOperand`,
`MirBorrowKind`, `MirPlace`, GPU/VHDL MIR types, and shared compilation-context
types across the mirrored `src/compiler/70.backend/**` and
`src/compiler/backend/**` trees. `mono/instantiation.spl` additionally reports
an untyped value-returning `instantiate` function.

This is not an LLVM, linker, runtime archive, or QEMU failure. The self-hosted
frontend is admitting mirrored/native compiler modules without resolving their
imported type surfaces consistently.

## Boundaries

- The native cache was preserved across all attempts.
- No Rust seed fallback was used.
- Three bounded verify/fix attempts were exhausted; do not restart this build
  in the same session.
- The ARM64 simple-core archive independently builds all 18 parts and satisfies
  the required-symbol admission set.

## Next investigation

Start a fresh scoped compiler session on current recovered `origin/main`.
Inspect entry-closure ownership of the mirrored backend trees and resolve the
first shared import/type-map divergence with a small compiler regression before
retrying the compiler-only Stage3 build.
