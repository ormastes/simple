# Bootstrap coalescing evaluates the present operand twice

## Evidence and cause

Frozen Windows source `7734f947be8ba9465d0ba312170681074e990587`,
`src/compiler/80.driver/driver_source_loading.spl:797`, contains
`content = file_read_nullable(path) ?? ""`.
The retained Rust-produced COFF object
`D:/dev/windows-release-7734-build-20261002/stage3/x86_64-pc-windows-msvc/stage2-native-cache/scope-3ad19b82e3f4bc0a/objects/7e44cede5913facf.o`
has SHA256 `d49022656d954812c169043de61c879e4749e9cfe74717a6099a07f3f2c4564e`.
The `_driver_cached_entry_source_scan` disassembly calls
`file_read_nullable` at offsets `30c7` and `30e1`; the latter lies on the
present branch after the nil comparison at `30d4`, before unwrap at `30e9`.
Disassembly receipt: `D:/dev/windows-nullable-source-evidence-20261002/source-collect.asm`.

Rust bootstrap HIR `lower_coalesce` cloned the operand expression into the
comparison and moved the same expression into payload extraction. Lowering an
expression once does not imply evaluating its two resulting HIR copies once.
This is a side-effect/evaluation defect; it does **not** establish the cause of
the separate Windows zero-source failure.

## Repair and scope

Bind the nullable operand to one immutable compiler local, then use that local
for the comparison and unwrap. Wrap the binding and existing conditional in a
value-producing block, as the existing if-let/try lowering already does.
Keep the nonnullable scalar fast path and all optional payload/result typing.
The pure-Simple MIR coalescing owner already stores the left operand once;
this repair is specific to the Rust bootstrap producer, not a production seed
fallback or a source-level workaround at the file reader.

## Regression and verification

`compiler/tests/coalesce_single_evaluation.rs` lowers actual syntax through HIR
and MIR and counts subject/default call sites, including nested coalescing and
nullable scalar arithmetic. The executable fixture
`test/fixtures/compiler/coalesce_single_evaluation.spl` checks side-effect
counters for nonempty, empty, Some, nil, scalar payloads, nested coalescing, and
lazy defaults. Success is exit 0 plus `coalesce-single-evaluation PASS`.

Source whitespace check passed. The first guarded offline Cargo cycle stopped
before tests because the sparse checkout lacked the counterpart C ABI header.
The exact header closure was materialized. The second cycle built that closure
but hit its 2 GiB RSS cap while compiling `simple-compiler` (peak 2,097,916 KiB,
exit 88, process tree quiescent). That cycle did not execute tests; this was
resource incompletion, not a semantic test failure. The second cycle also
introduced a default-feature-free Cranelift JIT test executing the counter fixture.

Receipts: `D:/dev/coalesce-single-evaluation-proof-20261002/guard.resource.env`
and `guard-cycle2.resource.env` with corresponding process-tree receipts and
stderr logs.

The third/final cycle changed only the resource cap to the admitted decimal
7 GB limit, preserving source, toolchain, feature flags, and Cargo cache. All
three tests passed, including native/JIT counter execution with the exact
success marker. Guard exit 0, postflight PASS, quiescent=1, enforced=1,
peak RSS 2,558,288 KiB. Evidence in the same directory:
`guard-cycle3.stdout.log`, `guard-cycle3.resource.env.process-tree.env`, and
`outer-cycle3-result.env`. Cargo used `--offline --locked -p simple-compiler
--test coalesce_single_evaluation --no-default-features --jobs 1` with one test
thread, nightly Rust `6368fd52c`, and a private target/TMP on D:.

This establishes the Rust bootstrap HIR/MIR and Cranelift JIT regression fix.
It does not qualify a rebuilt LLVM/COFF producer, cross-host bootstrap, or
deployment. No frozen producer was modified and no full hello verification
attempt was consumed. No further verification cycles were run.
