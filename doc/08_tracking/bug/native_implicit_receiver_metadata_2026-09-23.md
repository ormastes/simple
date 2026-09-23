# Native implicit receiver metadata

Status: scoped fix VERIFIED; independent Astra review ACCEPT. Source base:
`10d40d59a7b83d896e73d61c5e462937d192dcde`.

## Defect and intended contract

The Rust parser marks a class/struct method without an explicit receiver as
static. HIR later scans the body and injects self when the body uses it.
Native import arity has already read the static flag and omitted this
parameter. A cross-module call consequently shifts every argument; a
zero-argument accessor can dereference a small integer as its receiver.

The candidate moves the existing body scan to parser declaration handling.
Implicit instance methods expose the self parameter before import metadata
is recorded. HIR trusts the parsed static flag instead of changing the ABI
after registration. The old traversal is moved unchanged; this patch does
not expand language support for previously unrecognized expression forms.
Explicitly static methods have no implicit receiver. Existing receiver-free
factory classification remains unchanged.

The pure-Simple core parser already prepends self to nonstatic methods,
avoiding this particular declaration/body disagreement. This is not a claim
of full frontend parity: receiver-free factory inference differs already,
and explicit leading-me syntax is not part of this patch.

## Acceptance gates

- Parser metadata: class and value-struct implicit receivers, explicit self,
  mutable methods, true static methods, explicit static constructors,
  receiver-free factories, nested body use, and ten-parameter stack arity.
- Native behavior: local methods, imported/renamed owners, explicit self,
  nine explicit arguments plus receiver, static calls, constructors,
  factories, value receivers.
- Production GUI: original accessors; only the independently necessary owner
  import and optional binding corrections may accompany the fixture.
- Captured build/runtime elapsed time, RSS receipts, artifact hashes, and
  unchanged resource cap.

Parser test: `src/compiler_rust/parser/tests/implicit_receiver_metadata.rs`.
Native fixture: `test/fixtures/native/implicit_receiver_metadata/`.

Independent Astra review accepted the final source and parser/native/GUI
evidence after removing an inconsistent leading-me arity change and correcting
the parser test import. This does not establish full compiler-suite PASS,
bootstrap admission, full frontend parity, or publication.

The first verification command was interrupted after an unintended rustup
nightly synchronization caused by missing absolute RUSTC selection. Incident
evidence is preserved in this lane's
`build/evidence/implicit-receiver/TOOLCHAIN-INCIDENT.md`. Builds were stopped
until independently verified private toolchain recovery.

## Pinned-toolchain verification

The independently qualified private dated toolchain at
`/Users/ormastes/simple-tmp/rustup-pinned-20260916.kq7xQk` restored the exact
old rustc/Cargo bytes without changing the shared installation again.
`private-toolchain-authority.env` captures resolution for this lane.

The first pinned parser command encountered E0514 because the earlier
interrupted command had placed newer-compiler artifacts in the private debug
target. A fresh empty parser-only target avoids those incompatible artifacts.
No cache or evidence was deleted.

- Parser integration metadata tests: 4 passed, 0 failed, elapsed 39.89 s,
  sampled process-tree peak 814128 KiB.
- Moved receiver walker unit test: 1 passed, 0 failed, sampled peak 896784 KiB.
- Bootstrap-profile private seed rebuild: interrupted at the resource cap,
  exit 88, peak 5867648 KiB against limit 5859375 KiB. The compiler crate was being
  generated with codegen-units1 and thin LTO. There was no Rust compile error.
  The old copied seed hash remained
  `69b67b26e965e7fa3de2d292c2774980be15e84625dd382708092f848241dfce`.

The final private diagnostic build used codegen-units 16, LTO off, jobs 1,
and the unchanged cap. It passed in 223.64 s with peak 3198640 KiB. Its compiler
SHA-256 is
`939c54da4864f891e3de44db72908653f63d58139f7dec47006984f9e75e5be3`.
Nonfatal rust-objcopy stripping warnings reported missing @rpath/libLLVM.dylib;
the artifact is diagnostic-only and must not be promoted as bootstrap authority.
The exported DYLD_LIBRARY_PATH was insufficient across this verification
wrapper's system-executable chain. Canonical bootstrap's scoped helper-library
invocation remains required; this lane did not qualify stripping.

## Native and production behavior evidence

Evidence root:
`/Users/ormastes/simple-tmp/implicit-receiver-metadata-20260923/build/evidence/implicit-receiver`.
`BUILD.md` records exact paths, commands, source fingerprints, and limitations.

The native harness explicitly sets `SIMPLE_NATIVE_BUILD_RUST=1`, exercising
the changed Rust compiler. Two earlier attempts accidentally selected the
seed's default interpreted pure CLI: one stopped at SCV admission, and the
cold-init attempt stopped with observer failure (exit 89, quiescent cleanup).
Those attempts are preserved and excluded from functional evidence.

With the same fixture and frozen runtime capsule, the old compiler built two
modules and the executable exited 139. The fixed compiler built both modules
and the executable printed `implicit-receiver-metadata: PASS cases=7`.
The old/new native executable hashes are
`4052ec8c04bacdf582771314aa5063f7b300ba202add6e56e7964b605a0e1507` and
`a9377905f84ba198d5b0ca37a143e04153daf04e46477e212acc5968e4c02101`.
The fixed run took 0.34 s with max RSS 8667136 bytes.

The production GUI overlay compiled 141 modules, zero failures, and printed
`gui-markdown-optional-frame: PASS cases=7`. Controller/session/document
sources exactly match the original P0 files: no explicit-self workarounds.
Only GUI owner imports and optional-binding prerequisites were applied;
`gui-prerequisites.patch` records them. GUI compile took 12.70 s, sampled
peak 415552 KiB; execution took 0.34 s, max RSS 10403840 bytes. Its hash is
`c07f358fefd576a8ee23ba6cfdce73296aaa48dd43deaad8098e56235ba47c99`.

All accepted parser/native/GUI/build receipts have zero observer errors and
quiescent cleanup. The cap is sampled enforcement, not a kernel hard limit.
Native fixture compilation took 2.92 s before and 5.96 s after; the compiler
build profiles differ, so this is not a controlled throughput comparison.
Production-profile compiler performance qualification remains with the
bootstrap phase. The source change moves a linear body scan from HIR to the
parser and adds no new runtime operation beyond passing the required receiver.

Independent Astra final decision: ACCEPT scoped functional fix and evidence.
Documentation layout check found zero executable specs under doc/06_spec;
working direct-env runtime guard passed.
