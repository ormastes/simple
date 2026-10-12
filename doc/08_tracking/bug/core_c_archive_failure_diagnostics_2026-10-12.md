# Core-C archive failure loses its actionable cause

Status: OPEN — diagnostic repair candidate; original CI cause not conclusively identified.

## Observed failure

Native Linux x86_64 Cranelift CI job 114511038620 checked out
`e03e140986021cd276ac3491aa3c57152e20c661`. Rust seed and native-all builds
succeeded; native-build compiled 1,237 modules without module failures. Stage 2
link then failed with only `native-build could not build the core-C runtime
archive` naming `native-objects-g9IWAn/core_c_runtime`. The 586-line uploaded
stage2 log contains no C compiler error. Its upload contains nine log files,
without the tool-authority/PATH inventory or failed archive directory.

The workflow installed clang-18, lld-18, llvm-18-dev, FreeType, and libunwind.
This is not evidence that Cranelift requires the LLVM code-generation backend.
The native archive policy independently requires an LLVM archiver.

## Confirmed source defects and bounded reproduction

`native_project/tools.rs` converted archive-tool discovery, command spawn,
directory creation, and fingerprint-write errors to `None`. Failed C commands
had only a trace-gated contextual message. The outer config owner then replaced
all these causes with the same generic archive-build failure.

The pinned common archive detector tries unversioned `llvm-ar` and Homebrew
locations, then returns `ar`. The native-project policy rejects that GNU fallback.
A PATH containing only a versioned LLVM archiver therefore fails before any C
translation unit is attempted. The pinned Linux workflow installs versioned
packages but does not add their unversioned LLVM bin directory to PATH.
This is a reproducible candidate explanation, not proven historical causation:
the exact CI runner PATH and tool results were not preserved.

A focused Rust executable compiled the exact pinned discovery function bodies.
Two private PATH fixtures referenced the same real local LLVM 23 archiver:
under the name `llvm-ar-18`, detection returned `ar` and the policy rejected it;
under `llvm-ar`, detection accepted it. Both assertions passed. The versioned
fixture tests naming behavior; it does not claim LLVM 18 execution.
Every declared core-C input was present in the pinned Git tree.

## Diagnostic repair

Keep the existing tool policy, archive providers, command flags, parallelism,
cache fingerprint, and Option return contract. Print the failed operation before
returning None: source discovery, directory creation, archive-tool discovery,
C command spawn/exit, archive command spawn/exit, missing archive payload, or
fingerprint write. Child stdout/stderr remain inherited. The new command helper
formats details only on errors; successful builds retain the same operations.

Three native Rust tests execute the exact helper: a nonexistent command must
retain its path and OS spawn error, a real child exiting seven must retain its
status and arguments, and a real child exiting zero must succeed. All three
passed on Linux/SOSIX. The full changed Rust file also parsed with rustfmt.
Tests were run as a focused source-extraction harness to avoid rebuilding the
compiler; full compiler integration and fresh CI execution remain UNEXECUTED.
Windows, macOS, BSD, and SimpleOS execution remain UNEXECUTED.

This is a diagnostics change, with no memory/performance optimization claim.
No Rust seed was substituted for production tooling or tests, no full native
build was restarted, and no existing cache or failed build artifact was removed.

## Next diagnostic

At an authorized future attempt, preserve PATH plus resolved C/LLVM archive
commands and versions before building. Run the changed core-C builder against
its real source set independently of the 1,237-module compile; retain command
errors and the failed directory. If the archiver lookup fails, select the
installed canonical LLVM bin directory explicitly under the existing bootstrap
tool-authority policy. Do not add GNU fallback or claim CI recovery from these
focused tests.

Local evidence: `/mnt/c/Temp/simple-core-c-archive-diagnostics-20261012/`
contains pinned source copies, source identity, exact command/discovery harnesses,
real-tool identity, discovery receipts, and candidate patch. Historical logs:
`/home/ormastes/dev/simple-platform-ci-failures-20261012/linux-cranelift-stage2.log`
and `linux-cranelift.log`; archive
`/mnt/c/Temp/simple-linux-cranelift-failure-20261012.zip`.
