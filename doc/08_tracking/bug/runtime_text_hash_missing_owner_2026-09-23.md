# Missing runtime text hash owner blocks native dynSMF consumers

Status: fix proposed; focused native diagnostic passes; full Phase2 admission pending.

## Contract and cause

Commit `920b7c2dcb3` migrated `src/os/smf/dynsmf_session.spl` from
`extern rt_hash_text` to `std.common.hash.runtime_text.runtime_text_hash_v1`,
but did not include that module. Main `806f57ffbd88` still has its two callers
and no definition. Full CLI/host-GPU closure links therefore require an absent
symbol. The focused native fixture reproduces `_runtime_text_hash_v1` undefined.

REQ-RUNTIME-TEXT-HASH-001: preserve the prior `rt_hash_text` contract: FNV-1a64
over every UTF-8 byte, offset `14695981039346656037`, prime `1099511628211`,
modulo 2^64 arithmetic, signed i64 result. No normalization or zero termination.
Existing `.srchash` and `.ifacehash` decimal sidecars require no migration.
See [cross-lane contract](rt_hash_text_cross_lane_disagreement_2026-09-07.md).

## Minimal design

Add the missing common/hash leaf and its explicit export, without modifying
callers, import lowering, C runtime, or generic trait dispatch. Iterate bytes
directly, with O(n) time for length-bearing text and O(1) auxiliary memory; no byte-array copy,
syscall, allocation, mutable global, or host-dependent seed is introduced.
This is a non-cryptographic freshness hash, never an integrity proof.

## Acceptance and evidence limits

- Unit: `test/01_unit/lib/common/hash/runtime_text_spec.spl` freezes empty,
  ASCII, multibyte UTF-8, NUL, overflow/boundary, order and determinism vectors.
- Native: `test/fixtures/compiler/runtime_text_hash_v1_main.spl` requires the
  imported symbol to link and returns a distinct nonzero status per mismatch.
- Diagnostic compiler: admitted Stage2 source `70748fd0`, SHA256
  `7f6283bc9a2b7e9d7ef7078b5c3bc7fbba49a54d3d6b61f83bb3cd0540a55821`.
  Source under test is main `806f57ffbd88` plus this patch. This mismatch is
  deliberate focused diagnosis, not current-main admission.
- Private outputs: `build/evidence/runtime-text-hash-v1/`. Pre-fix Cranelift
  compile/link fails on the exact missing symbol in 2.68 s, 138559488-byte RSS.
  LLVM is unsupported by this admitted tool; no seed fallback was used.
- Post-fix: 2 modules compiled, 0 failed, 55 KB linked in 3.07 s, compiler RSS
  139395072 bytes. Native fixture exits 0 on all ten checks; execution RSS
  8732672 bytes. SHA256 of the diagnostic binary:
  `d54926f56c2bbdb62230b5a2cf1963a3689f0e5ca84284b21bc0633a3864ba93`.
  `nm -gU` reports `_runtime_text__runtime_text_hash_v1`; recompiled callers
  resolve that canonical symbol. Existing cached unresolved caller objects must
  be rebuilt, not merely relinked against the new owner.
- Complexity/no-copy claims are structural; short fixture timing does not prove
  throughput parity with the legacy C runtime. No such benchmark claim is made.
- Astra review identified a legacy representation limit: `rt_string_byte_at`
  scans raw-pointer text for NUL on each access (C `runtime_native.c` and
  pure-Simple `core_string.spl`), making this fallback potentially O(n²).
  Embedded NUL requires length-bearing text. Native vectors prove the selected
  admitted runtime representation, not all text producers/runtime variants.
  Cross-runtime representation and performance parity remain admission blockers.
- General SSpec/docgen/core/MCP gates require an admitted general runtime and
  remain unexecuted; no production verification PASS or full-CLI claim.

Scope/ownership: only this hash leaf, focused tests, and this report. Parallel
import/alias/provider fixes are separate. Full builds need parent approval.
Independent Astra review is required; lower-model sidecars are N/A for this leaf.
