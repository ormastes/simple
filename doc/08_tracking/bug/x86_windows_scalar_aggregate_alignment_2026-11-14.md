# x86 Windows aggregate layout disagrees with scalar ABI

Status: source fix implemented; targeted host-native diagnostic passed.
SSpec execution and native Windows qualification remain pending. This change covers x86 Windows MSVC and GNU scalar
alignment, not ARM/RISC-V or additional SimpleOS target support.

At inspected source revision `465ac94e28fa53b8db81aa7e69ead1e78d6771ea`,
TargetHIR scalar resolution gave Windows i64/u64/f64 alignment 8, but the
typed and legacy MIR aggregate paths called architecture-only layout. Its x86
baseline aligns these fields to 4. The i686 COFF LLVM datalayout likewise
omitted i64 alignment and explicitly set f64 ABI alignment to 32 bits.

The parent agent compiled a C reference using Clang 23. The source is
`/tmp/simple-x86-layout-reference-20261114.c`; retained local LLVM outputs are
`/tmp/simple-layout-<triple>.ll`. For `{ unsigned char; long long; void*; }`:

| Target | i64/f64 alignment | Record size/alignment | Value/pointer offset |
|---|---|---|---|
| i686-pc-windows-msvc | 8 | 24 / 8 | 8 / 16 |
| i686-w64-windows-gnu | 8 | 24 / 8 | 8 / 16 |
| i686-unknown-linux-gnu | 4 | 16 / 4 | 4 / 12 |
| x86_64-pc-windows-msvc | 8 | 24 / 8 | 8 / 16 |

These are compiler-emitted C constants, not execution of a Windows program or
proof that Simple currently matches them. The regression oracle uses these
fixed values independently of the Simple implementation.

One pure common scalar policy now supplies the x86 Windows override to HIR
scalar and aggregate field layout. Target-aware aggregate layout threads the
policy through the existing C, default/reordered and transparent algorithms;
packed layout keeps byte alignment. Existing architecture-only entrypoints
retain their baseline results. Both MIR paths use the target-aware entrypoint.
The Windows i686 LLVM datalayout adds i64:64 and f64:64; Linux and f80 are
unchanged.

Direct context aliases accepted by the architecture parser are canonicalized
through the existing MIR normalization authority before scalar policy is
applied. The narrow bitfield scenario checks storage-unit alignment only; it
does not claim full Microsoft bitfield allocation compatibility.

Authored evidence:

- `test/01_unit/compiler/50.mir/x86_windows_layout_contract_spec.spl`
- Shared behavioral assertions: `test/fixtures/compiler/x86_windows_layout_contract.spl`
- Native diagnostic entry: `test/04_smoke/bootstrap_x86_windows_layout_contract.spl`
- Manual: `doc/06_spec/01_unit/compiler/50.mir/x86_windows_layout_contract_spec.md`

The host-native diagnostic imports actual compiler owners and checks explicit
target layout values. It does not qualify Windows machine-code execution,
cross-target calling convention, the whole test runner, or bootstrap Phase 3.
The targeted diagnostic compiled and ran against clean source revision
`8703189ecd848ec6114b81394cb9a0a81cc3a565` on `aarch64-apple-darwin`:
239 compiled modules, zero failed modules, build/run exit 0, and stdout
`x86-windows-layout-contract-ok` after all five contract groups asserted.
Producer SHA-256: `1428b5b7bd447058193626388b5e178dabb2913d059e03fa68b47e99c4bc9d93`.
Binary SHA-256: `648a4db44a20e021db7d7ff29b6bfb90ee50d17a40627fe470136cdf0d28d733`.
Local evidence: `/Users/ormastes/simple-phase3-recovery-16e6180752d/.simple/storage/build/bootstrap/x86-windows-layout-8703189-diagnostic/evidence.sdn`; sibling `build.log` and `run.log` retain the execution logs.
The core-C-bootstrap runtime diagnostic used a private cache and one attempt;
nonfatal compiler/runtime diagnostics are recorded in that evidence file.
This documentation update does not change the executed source or tests.
The SSpec runner was not executed. Windows binary execution and end-to-end
cross-compilation remain unqualified. Provider token usage and comparable
cost cohort are unavailable; no ratio is inferred.
