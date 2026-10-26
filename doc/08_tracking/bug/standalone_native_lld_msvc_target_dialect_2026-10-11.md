# Standalone native LLD selects GNU arguments for an MSVC target

Status: PATCH_APPLIED_LOCAL_NATIVE_HELLO_PASS_FULL_CHECKS_PENDING. Bug DB reconciliation is
pending because no qualified pure-Simple database tool is available.

## Reproduction and affected owner

The recovered bootstrap seed
`0b443ab26ff8ff26d62041fd9fb67b999f9d5f39ad81fcfc2fa62d66b224702e`
compiles an explicit `fn main() -> i64` with `compile --native
--backend=cranelift --linker=lld --no-pie --map`. On Windows/MSVC, the command
selects `lld-link` but sends GNU `-o`, `-Map`, `-L`, `-l` and other GNU options.
The actual compile exits 1 and no executable is produced. The selected runtime
library in that historical invocation was not independently bound.

The affected path is `LinkerBuilder::link -> NativeLinker::link`, whose command
selection and argument selection did not retain one target/flavor decision.
The standalone Windows library defaults also selected nonexistent `c.lib`.
The C compiler helper recognized `cl` but not `clang-cl` as an MSVC driver.

This is distinct from the compiler-driver issue documented in
[the earlier MSVC driver report](stage2_msvc_link_uses_gnu_driver_flags_2026-09-12.md).
Do not reopen that resolved issue or claim its fix covered this separate owner.

## Applied repair and regression evidence

The local repair carries the selected target to command construction, uses one
COFF argument owner for `link.exe` and `lld-link`, retains GNU and Wasm frontend
selection, and rejects incompatible linker families before process launch.
MSVC libraries use canonical Windows defaults without `c`; existing `.LIB`
suffixes are retained. Driver classification recognizes `clang-cl` independently
of target ABI. The older shared common file is preserved with five missing
Windows support libraries added; a release-based producer uses the tested
release candidate so released defaults are not discarded.

Eight actual Rust owner regressions passed: six command/dialect controls and
two default-library controls, including Windows GNU preservation, explicit
MSVC, Linux-on-Windows, Wasm, incompatible families, spaces and library suffixes.
These are focused tests of the real owners, not a mocked target/linker.

Receipt:
`build/phase2-six-products-80030-20261010/independent-next-step-review/producer-admission-repair/native-linker-dialect-tests-cut4/attempt2/RESULT.json`.
Request SHA256:
`32efab4790f8278fdc4276f7cdf3cdbf6b398c9b9792729499dbf3ee6af09488`.
All eight passed, zero failed/ignored; source/tool pins remained stable and the
Windows Job closed. Cargo requested forty jobs. The first preparation attempt
failed before Cargo because an 8 GiB RSS request exceeded the collector's
supported 5 GiB bound; that failure remains recorded, not counted as a test.

## Pure-Simple parity and remaining acceptance

Source review of `native_linking.spl` and `MsvcLinker` found an existing Windows
MSVC route emitting `/OUT`, `/LIBPATH` and `/ENTRY`. It does not show this same
dispatch defect. This is source review, not executed pure-Simple validation.

Before resolving the bug, rebuild into an unlocked output from exact sources,
pin the actual runtime/tool/SDK inputs, and successfully build and run native
Hello. Exercise the full native builder's updated Windows-default test and
actual C-shim compilation. Preserve existing in-use admitted generations.
The recovered seed has no LLVM backend feature; its LLVM rejection is a
separate capability gap. No full bootstrap, performance improvement or Phase 2
test-product qualification follows from these eight passes.

No temporary stub, forced unresolved-symbol option or duplicate runtime owner
is introduced. The introducing fix commit/PR must be recorded after landing;
the source application is currently uncommitted.

## Cached producer rebuild evidence

The explicitly authorized successor rebuild completed on 2026-10-11 with
`PASS_PROVISIONAL_CARGO_BUILD`. Cargo reported 267 fresh artifacts and 26
rebuilt artifacts, completing in 4m 26s with forty jobs requested. The exact
compiler SHA256 is
`0f2b8375f3283503675dfcabe6a71c311adaaa16c9e247e0558845163effa4ec`.
The authoritative receipt is
`build/minimal-native-producer-20261011/RESULT_EXCEPTION1.json`.
The process tree closed with peak sampled RSS 3,750,628 KiB.

This rebuild alone establishes a seed artifact, not native-Hello success,
pure-Simple performance, or producer admission. At build completion the original
native-Hello ledger was 2/3; only its final cycle remained available.

## Actual successor native-Hello result

That final cycle subsequently completed with
`PASS_PROVISIONAL_CRANELIFT_NATIVE_HELLO` in
`build/native-hello-final-20261011/RESULT.json`. Version, interpreter Hello,
native compilation and native execution all passed with separate complete
stdout/stderr capture, authentic closed process-tree receipts and stable input
pins. The actual `lld-link` invocation used COFF `/OUT`, `/MAP`, `/LIBPATH` and
`/WHOLEARCHIVE` arguments; no GNU arguments were sent to that driver. Its first
runtime library path resolved to the successful Cargo build's archive, SHA256
`92d43c7fa360e5a77f94effe2b7ca4db276518e1c9e8933a79123a36c316cdd9`.
The retained entry object and C shim produced a real PE executable, SHA256
`165aa8589b59240b17cda5091a47ebf6bf887aa12ccef4bccb7ecace98c6c618`,
which printed exactly `Hello native seed` and exited zero.

Actual child wall times were 0.0723 seconds for version, 0.0677 seconds for
interpreter Hello, 1.5218 seconds for native compile including link, and 0.0906
seconds for native execution. Compile-tree peak sampled RSS was 140,644 KiB.
Link-only time was not separately measured. This does not prove the 0.1-second
pure-Simple/TLDR target, full compiler checks, or Phase 2/3/4 qualification.
The native-Hello ledger is now closed at 3/3 with this passing result; do not
replay it. Full builder regression and required core checks remain outstanding.
