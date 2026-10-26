# Smux typed-key codec independent Astra review — 2026-10-26

**STATUS: WARN — one P2 source finding; execution NOT_RUN.** This frozen
candidate is not admitted for allocation-safe encoding or full CoreMux support.
Base HEAD: `4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`, worktree
`D:/dev/simple-coremux-shared-20261025`. Unrelated dirty lanes were preserved.

## P2: temporary encoding allocations can fail without a typed refusal

`core_mux_key_codec.spl:107` and `:117` trust arrays returned by
`smux_one_key_bytes`. Named, Function and Scalar base helpers construct literal
arrays without checking their allocation or expected length. Checking the final
output and optional Alt-prefix allocation does not check those base arrays.

Owned runtime source permits allocation failure to return zero
(`src/runtime/simple_core/core_array.spl:217`), and reports invalid-array length
as zero (`:270`). The hosted owner likewise reports null-array length as zero
(`src/runtime/runtime_native.c:9793`). Thus a failed second-pass temporary can
contribute no bytes while the codec returns `Ok(output)` with a zero-filled tail.
A first-pass failure can instead undercount capacity. Alt can prepend ESC to a
failed base. These are source-derived failure paths, not executed reproductions.

Validate every temporary against an independently determined expected length,
including Alt's base, or encode directly into one checked bounded buffer.
Add a deterministic mismatch/failure oracle proving `Unavailable/NotApplied`
instead of successful missing/zero bytes. Checking only a temporary's reported
length against itself is insufficient for a shortened allocation result.
The existing 17 cases have no allocation-failure oracle; documentation admits
that limitation. Findings were sent to root and author before this report.

## Other source observations

All 13 Named mappings, normal/application cursor variants, F1–24 and UTF8
boundaries match the local policy tables. Scalar validation precedes modifier
handling; unsupported combinations return typed errors without silent flag loss
or keyboard-layout guesses. Normal-path arithmetic is bounded: 256 keys,
seven bytes each, 1792 maximum; subtraction guards capacity before addition.
The codec mutates neither its inputs nor any queue/VT/API state. Error fields
consistently express context-free request ID zero and NotApplied.

The 17 cases call production code and use literal byte/error oracles, with no
placeholder passes. The 17-row manual accurately summarizes them; it contains
no executable source block and is not docgen evidence. The native plan correctly
requires an exact raw-input oracle and real owner dispatch before qualification.

## Exact reviewed SHA-256 pins

| Path | SHA-256 |
|---|---|
| `src/os/apps/smux/core_mux_key_codec.spl` | `0ec80a4e6adf2df2d7fc2898c096e89da326b7ca13f3af7f468366e602d70488` |
| `test/01_unit/os/apps/smux/core_mux_key_codec_spec.spl` | `f420c76b4a138d8e25098756f2c1fca1b972ccb7403c8aab6179f85acd63a72a` |
| `doc/06_spec/01_unit/os/apps/smux/core_mux_key_codec_spec.md` | `5ff2286901733da15245d936002688928d7e24562f604a08e84e1643ffa518ce` |
| `doc/03_plan/sys_test/smux_typed_keys_2026_10_26.md` | `314f5699cc2fd69eed31a0a2220f5c67bd6894e7dedfb46ca69581eb71d03d72` |
| `doc/09_report/smux_typed_keys_source_2026_10_26.md` | `e11b26bcd5b8093fa423845dfff28e204d4e094e4d97f7164e389eb11e06de60` |

## Limits

No compiler/build/test/docgen/native execution, production edits, staging or
commit occurred. Runtime value semantics, allocation faults, coverage and
performance remain unmeasured. Unsupported modifiers, dispatch integration,
TERM/terminfo compatibility and raw child observation remain qualification
gaps. No Native/full-provider or tmux wire-equivalence claim is admitted.
No retry budget was consumed or reset. This review adds only this report.

## V2 focused review — allocation finding closed at source

V2 base HEAD: `fd744829aea0e0d7f568cd2286702a1a9cf37c2d`. All five
author-supplied pins matched. **STATUS remains WARN / execution NOT_RUN.**
The preceding V1 finding and pins are historical and remain unchanged.

Every Named, Function, Control and UTF8 literal now enters
`core_mux_key_bytes_checked_v1` with its independent constant format length.
The seam rejects invalid expected sizes and uses the existing pointer/exact-length
guard. Both encoding passes propagate that error before counting or copying.
Alt derives its prefix size only from an admitted base, checks its allocation,
then copies; final copied count must equal preflight size. No source path from
the reported missing/shortened temporary to successful key omission,
undercount or zero-filled tail remains. The V1 allocation P2 is closed for this
source delta, without claiming actual allocator-failure execution.

Two new cases exercise the production seam with empty/short/long carriers,
invalid expected lengths and successful exact lengths 1–7 including NUL.
The manual and plan accurately retain NOT_RUN and distinguish deterministic
mismatch admission from real OOM/null-pointer injection. Unchanged mapping
criteria were not reverified.

**Review correction:** the reviewer initially reported a missing `MuxErrorV1`
test import. The author challenged that reading; focused line/hash inspection
confirmed that V2 line 4 already imports `MuxErrorV1`, with the same frozen
spec hash. That report was a reviewer reading error and is retracted; no author
change was needed. Root and author were notified. There is no remaining scoped
source finding in this V2 review; qualification remains WARN / NOT_RUN.

| V2 path | SHA-256 |
|---|---|
| `src/os/apps/smux/core_mux_key_codec.spl` | `52bbf1868146cf66b3be6563de06abdbf5273fe87a9403a9b1e1b868299333f7` |
| `test/01_unit/os/apps/smux/core_mux_key_codec_spec.spl` | `914a7df038bd1cf760d74ee8d1d0cd844c0543e938bda88bde0b367ddd057ddf` |
| `doc/06_spec/01_unit/os/apps/smux/core_mux_key_codec_spec.md` | `4a68a040228b978646f68839ed2f30bfa8f96a7d51885e963efa38177cd92af2` |
| `doc/03_plan/sys_test/smux_typed_keys_2026_10_26.md` | `5f2fbd790191f9bcbac6409c1f64367f6ccc0ea3ed3a8723d3c64204a78329c7` |
| `doc/09_report/smux_typed_keys_source_2026_10_26.md` | `0a12d229aeca43e2a9eaf517ab473c945761c4106ea484b2e8c3730dbb385de1` |

No executable, production edit, staging or commit occurred. Modifier policy,
dispatch, TERM/terminfo, raw-child and runtime qualification gaps remain open.
