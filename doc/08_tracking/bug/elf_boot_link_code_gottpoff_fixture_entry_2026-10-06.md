# CODE_4/CODE_6 GOTTPOFF fixture selected an undefined entry

The Phase1 collector's ordinal20562 executed47 examples in
`test/unit/compiler/backend/linker/elf_boot_link_spec.spl`:46 passed and only
"writes CODE_4 and CODE_6 GOTTPOFF through one SimpleOS TLS slot" failed.
Its TLS_IE_SCRIPT selected `read_imported_tls`, while the actual checked-in
`code_gottpoff_x64.o` defines `_start`. Assembly and llvm-readelf's symbol table
agree. `elf_boot_link.spl` rejects an undefined entry before the example's
relocation assertions; the structured result does not retain the exception.

The fix selects `_start` only for this object's layout plan. All four original
GOT-size, displacement and TPOFF assertions remain unchanged. Other layout
plans and production linker code are unchanged.

## Actual evidence and qualification

- Original result: `/tmp/simple-phase1-per-row-attempt-20261006/20562/result.json`,46/47,zero skipped.
- Changed original file:47/47,zero failed/skipped,5502ms; private overlay artifact
  `/tmp/simple-elf-code-gottpoff-fixture-fix-20261006/build/test-artifacts/unit/compiler/backend/linker/elf_boot_link/result.json`.
- Root launcher observation: `/tmp/simple-elf-code-gottpoff-fixture-result-20261006`.
- Kernel receipt: `/tmp/simple-elf-code-gottpoff-fixture-kernel-20261006/kernel-containment-terminal.env`,exit0,quiescent1.
- Compiler SHA256:`0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`.
- Dependency source:`e59027c353e9ed6ea8ddf572424da70e188fe511`; isolated changed spec SHA256:`3794e25b2f627e4c871bf2d323337a60e07936634a23f6d6bedf5596ce07721b`.

This is authorized Phase1 diagnostic seed evidence for a test-fixture correction,
not self-hosted compiler/native-library or whole-Phase1 release qualification.
No already-green test was replayed after the changed file passed. The canonical
manual generator completed separately without executing tests. No new feature requirement,
architecture, runtime API, or performance behavior is introduced. Sidecar
review is N/A for this one-line test-only correction.

Provider input/output/cache-read/cache-create tokens: unavailable. Comparable
cohort average and ratio: unavailable; no usage values were guessed.

## Manual-generation receipts

The first docgen-only attempt hit watchdog150s (kernel exit124,quiescent1)
without writing a manual. Receipts remain in
`/tmp/simple-elf-code-gottpoff-docgen-20261006` and
`/tmp/simple-elf-code-gottpoff-docgen-kernel-20261006`.
A single changed-budget continuation used 1GiB/420s, root450s and exited0,
kernel quiescent1: one complete manual, zero stubs. Receipts remain in
`/tmp/simple-elf-code-gottpoff-docgen-cycle2-20261006` and its corresponding
`/tmp/simple-elf-code-gottpoff-docgen-cycle2-kernel-20261006` directory.
The reviewed manual lists47 active examples and preserves this case's four
assertions and corrected ENTRY. Existing docgen export-use and runtime-family
warnings are unrelated to the fixture change. No test replay occurred.
Original JSON SHA256:`137a0d38e2787c1da3da4d307e8471260093b7c50922bb46e2223bec56094149`.
Changed JSON SHA256:`3cb9cd61059a454f4510c6d0b7007aa891a97657b9aa605c65912623ed21b693`.

The single source/manual SSpec scan exited0, kernel quiescent1, aggregate74,
release_ready=true,blockers0. Dimensions:narrative80,structure60,oracle70,
traceability80,evidence100,coverage100,maintainability20. Its low-level manual
warnings concern existing scenarios' step flow, general narrative and REQ
metadata. No new feature requirement is fabricated for this fixture correction.
The scanner's stale warning specifically checked for a source hash string absent
from canonical docgen output; a reviewed provenance header now records the
actual source SHA and generation receipts. The generated body remains unchanged.
All47 scenario statement bodies match current source after docgen indentation
normalization; this scenario's four assertions match the original byte-for-byte.
No scan was replayed. Evidence:/tmp/simple-elf-code-gottpoff-sspec-scan-20261006.
