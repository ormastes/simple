# LLVM unsigned classifier received its instance instead of its type argument

Status: source correction authored; verification pending. The three diagnostic
cycles are exhausted. No fourth diagnostic or fixed-producer PASS is claimed.

## Required regression and provenance

Source6772d23f5e2b5bd79c22152780d5183440ac342e, pure Stage2 SHA256
569203737fe7bdfafd6f52cfe1c1c8d6a30ed17b741217a08c267058e2f8283c compiled the
unchanged unsigned_integer_suffix_boundary fixture through the single positional
native-build route. It returned101 at MAX_U64 >>32. Its object stores all64 bits
correctly, then performs a signed shift. Original evidence:
`/mnt/simple-bootstrap-6b2/linux-6772-u64-native-pure-stage2-20260929`.

## Actual first observed loss

Final read-only debugger evidence:
`/mnt/simple-bootstrap-6b2/linux-6772-unsigned-debugger-probe-20260929`.

- 19 decoded lower_type returns:16 U64 kind discriminant2738799268 and3 I64
  discriminant258540933. U64's discriminant is independently visible in the
  classifier's final comparison constant0xa33ec2a4.
- All95 is_unsigned_mir_kind entries receive the same non-enum instance value
  (first byte64/discriminant0), rather than a MirTypeKind enum (heap kind7).
  Every call returns raw19, the false value in the generated classifier.
- All55 get_operand_unsigned returns are false. The captured9304-byte LLVM IR
  contains6 ashr and1 sdiv, with no lshr or udiv.
- At llvm_cast_impl address0xa1d96d, target.kind is loaded into RSI; at0xa1d976,
  self is placed in RDI. The call at0xa1d979 targets is_unsigned_mir_kind. Its
  entry saves RDI at0xa26cc5 and checks that value as the enum. Caller and callee
  therefore disagree on the receiver argument.

The source declared `fn is_unsigned_mir_kind(kind: MirTypeKind)`, yet every
production use invokes it through self. The bootstrap parser's class method
rule marks self-less fn declarations implicitly static; the callee takes one
argument. Adding explicit immutable self makes its declaration match the
existing receiver calls. This changes no MIR enum, AST layout, or literal value.

The general compiler inconsistency remains separately open: accepting an
instance call to an implicitly static class fn must either lower the receiver
consistently or reject that call. This narrow correction makes the classifier's
intended instance-method contract explicit; it does not fix all such calls.

## Diagnostic limits

Cycle1 accidentally used --source/--entry and selected embedded Rust FFI;
its results are not pure qualification. Cycle2 used the matching single
positional pure route: all six unsigned boundaries failed, signed control
passed. Cycle3 compiled under the debugger and did not run the probe binary.
It completed32.49s with unchanged pins and no remaining owned processes.

The debugger's HIR payload offset24 does not match the producer runtime layout;
those payload words are excluded from the conclusion. Enum discriminants,
compiled register transfers, classifier returns, and captured IR support the
diagnosis independently. No observation limit was reached.

## Authored acceptance

REQ-LLVM-UNSIGNED-RECEIVER is covered by
test/01_unit/compiler/backend/llvm_unsigned_classifier_receiver_spec.spl:
four unsigned widths, signed/noninteger controls, and cast-to-shift/division
IR propagation. These four cases/eighteen assertions are authored, not run.
The unchanged original native fixture must pass with a refreshed pure producer
before native qualification. Existing passing signed diagnostics are preserved.
