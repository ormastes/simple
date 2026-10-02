# Bootstrap COFF partial linking and duplicate runtime globals

Date: 2026-10-02. Base: `0d722af3d6`. These are separate failure groups;
their counts are recorded attempts, not numbers of distinct compiler defects.

## COFF partial linking: F0026 and F0049

Both attempts compiled `src/compiler/99.loader/completeness_seal/axis_parse.spl`
with the LLVM backend, in Windows phase 3 and phase 4 respectively.
`driver_aot_native_output.spl` passed multiple object files to `ld.lld -r`.
That is the ELF driver, while both retained `dynamic_identity.closure.o`
inputs are valid AMD64 COFF: `llvm-readobj --file-headers` reports
`COFF-x86-64`, machine `0x8664`, 49 sections, 155 symbols, no optional header.
The phase-4 object pair is 12,171 and 3,949 bytes. This is not evidence of
truncation, an ELF target, or a malformed `.o` extension.

The new pure command plan selects GNU PE partial linking (`ld -m i386pep -r`)
for Windows AMD64, `i386pe` for Windows x86, and prefixed GNU cross-linkers
for those COFF targets on non-Windows hosts. The subprocess runs through
the SOSIX host facade. Single-object copy behavior is unchanged. Unsupported
COFF architectures fail explicitly; the existing non-COFF `ld.lld` route
remains unchanged and does not establish Darwin/wasm partial-link support.
GNU PE-capable binutils must be available on PATH; `lld-link` cannot replace
this operation and an archive is not treated as a relocatable object.

## LLVM global redefinition: F0003

The recorded source is `src/app/any_audit/classify.spl`, whose public
`ANY_CLASSES: [text]` global receives provisional storage in `lower_static`
and finalized runtime storage in `lower_runtime_module_initializers_named`.
The producer's struct-keyed `SymbolId` dictionary defect is documented in
`_MirLoweringExpr/expr_dispatch.spl`; numeric identity is already used for
the authoritative global lookup mirror. Normal LLVM emission consumes every
dictionary value, while bootstrap LLVM emission has a name-deduplication path.
The retained log reports duplicate internal `@g_...__ANY_CLASSES` definitions;
the temporary `module.ll` no longer exists. The exact source diagnosis is
therefore supported by the producer code path, but not yet by a native rerun.

Finalized static replacements are collected during initializer lowering and
merged once per module by numeric symbol identity. This preserves the finalized
type/value, distinct symbols with conflicting names, and unrelated entries,
without depending on dictionary iteration order. Work is O(S + D) for S stored
entries and D finalized globals, rather than rebuilding S entries D times.

## Validation status

- Existing artifact inspection: PASS, both retained COFF objects identified.
- GNU ld 2.42 read-only capability check: `i386pep` and `i386pe` supported.
- Source whitespace check: PASS.
- Independent source review: requested; initial quadratic implementation
  finding corrected to one batch compaction per module.
- Added executable specs cover replacement identity, batch finalization,
  an actual ANY_CLASSES frontend-to-LLVM definition count, and linker plans.
  They are UNRUN pending an admitted compiler/test slot.
- First guarded linker probe: NOT LAUNCHED. Windows owner authorized a
  256 MiB/30-second slot, but the session helper failed its compiler identity
  query before child creation (`exit_status=89`, `root_pid=0`, `quiescent=1`).
  Receipt: `D:/dev/bootstrap-link-probe-20261002/process-tree.env`.
- Corrected owner-admitted linker-only probe: PASS. Sourced the pinned Windows
  build environment before the helper, then linked the exact F0049 input pair
  with GNU ld under the 256 MiB/30-second Job. Receipt
  `D:/dev/bootstrap-link-probe-20261002/probe2-process-tree.env` reports
  `status=complete`, exit 0, `quiescent=1`, verified helper, peak RSS 2,588 KiB
  and peak Job commit 7,736 KiB. Output is relocatable `COFF-x86-64` AMD64
  (4 sections, 214 symbols, optional-header size 0). All 13 input external
  definitions survive; no names are missing. Output SHA256:
  `4503dffcc84780e47e07a66d75a3dba912845d5621f75bda970c1fdaca8b6215`.
  This proves the external linker strategy, not execution of the patched driver.
- Full compiler/lib/MCP/LSP checks and native smoke: UNRUN. No verification
  PASS, release qualification, live bootstrap deployment, or resolved claim.

Inputs remain under `D:/dev/bootstrap-memory-fix-validation-20261002` and were
not changed. Exact attempt/log/cache identities are in
`D:/dev/bootstrap-failure-catalog-20261002/failures.json`.
