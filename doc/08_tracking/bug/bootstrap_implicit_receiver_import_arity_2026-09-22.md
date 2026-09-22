# Bootstrap cross-module implicit receiver omitted by arity metadata

Date: 2026-09-22. Source baseline: `b74a4b94bbb03151b36954423798abae29c2e4c3`.
Status: generic compiler defect OPEN; explicit-self signature containment
native VERIFIED. No Stage2 admission, general compiler-test PASS, or push.

## Root cause

The frozen bootstrap producer generates a callee expecting self but a caller
that omits it. The current source exposes the disagreement:

- `src/compiler_rust/parser/src/types_def/mod.rs` class and struct method
  parsing marks `fn method(args)` with no explicit self/me parameter as static.
- `src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs`
  injects implicit self when the body uses self, even when `is_static` is true.
- `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`
  `method_arity` accounts for implicit self only when `is_static` is false.
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` drops the leading
  operand whenever the argument count exceeds registered arity by one. Its
  comment describes a nil module receiver, but the code does not check nil.

This explains the observed cross-module signature mismatch; it is not a
constructor allocation failure or fixed by adding a type to the receiver local
or by passing it through a typed free-function parameter. Generic repair must
unify method classification/arity with actual callee lowering and distinguish
module qualification from instance receivers. That repair remains open; this
lane does not rebuild or mutate the frozen bootstrap authority.

## Minimal native evidence

Fixture: `test/fixtures/native/receiver_transport/{support,local,typed}.spl`.
Evidence root (absolute):
`/Users/ormastes/simple-tmp/bootstrap-receiver-transport-20260922/build/native_probe/receiver-transport`.

Authority:
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.
Producer SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.

Two cycles only. In cycle 1 support methods used implicit self. Both two-module
builds passed, then both runs exited 139. `typed-red.disasm` shows `typed_read`
overwriting x0 with 7 before calling `read_marker`, while the callee dereferences
x0 as self. `typed_stack` similarly shifts explicit arguments into x0..x7 and
stores only 9 to the stack although its callee expects two stack arguments.
The red run dies in `typed_read` first, so its `typed_stack` observation is
disassembly evidence only, not a separately executed red stack assertion.

In cycle 2 the sole source change was explicit `self, ` in both support method
signatures. Both builds and runs pass. Actual outputs are `local=107`,
`typed=107`, and `stack=145`. `typed-green.disasm` leaves self in x0, puts 7 in
x1 for `read_marker`, and emits two stack stores (8 and 9) for `stack_sum`.
Correctly registered methods can therefore transport more than eight arguments
in this frozen producer. This does not establish why the separately preserved
production freeze caller truncated three arguments or repair that call.

Binary SHA-256 values:

| Artifact | SHA-256 |
|---|---|
| local red | `0340e8450b9a3968fc37ba15d254110a52cb85bf2ff8062271fd1d24e36c9a0a` |
| typed red | `c4efd0c615ddd8821467d71194c687a05a336f00258762895534064b8a9256c2` |
| local green | `9b873c37cdaa8f1955dd9629b69bcc580ea754c76297a00d741ae747ebb439b5` |
| typed green | `ea6b50dafa06feab282c1a265b44a18e3b5e0f68b284b3922b502e4a91cee79d` |

## Resource evidence and containment scope

Red/green local build elapsed: 2.49/2.44 seconds; typed: 2.34/2.31 seconds.
Largest sampled build process-tree RSS across all four: 202064 KiB.
Green local/typed executable max RSS from `/usr/bin/time -l`: 8634368/8683520
bytes; both took 0.34 seconds. Short-run sampled RSS is lower because sampling
can miss transient peaks. These tiny runs do not establish production throughput.
All eight receipts show zero observer errors and quiescent cleanup, below
5859375 KiB. The cap is sampled enforcement, not a kernel hard limit.

Explicit self changes metadata/argument placement, introducing no allocation,
loop, scan, or added runtime call. It preserves the existing instance-method
semantics. Apply it to the affected capsule definitions (including supporting
identity/context methods) in production and in the extracted fixture, then
verify that full projection separately. Merely changing the fixture call or
typing its receiver cannot correct the definition-side import arity.

No generic language workaround is silently normalized: this report retains the
implicit-self defect as OPEN. This lane adds the reproducer and verified
containment evidence, not a claimed general compiler repair.

Independent Astra review: PASS for the scoped containment evidence and report.
The reviewer inspected all eight receipts, disassemblies, hashes, and the
parser/HIR/import/call sites without rerunning green tests. Full capsule
projection acceptance and generic compiler repair remain separate open work.
