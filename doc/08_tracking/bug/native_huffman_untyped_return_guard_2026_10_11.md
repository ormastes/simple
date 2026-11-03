# Native Huffman return contracts block object generation

Status: OPEN (P1); tagged application-source workaround, compiler type inference unresolved.

Normal producer 4cca9585 (source 5bebee246) rejects unannotated bitstream_new during HIR: a value-returning function has no declared return type. Baseline: `/mnt/c/Temp/simple-manual-huffman-4cca-20261011/epoch03/evidence.json`. Existing tracked source annotations were reused, preserving bodies; a second tagged change declares the existing code-table array parameter because MIR otherwise treats `for existing_code in codes` as i64. Neither workaround disables validation.

Changed module normal AOT: exit 0, real Huffman definitions, object 49312 bytes. Receipt: `/mnt/c/Temp/simple-manual-huffman-4cca-20261011/workaround02-storage-recovered/evidence.json`. Cache-preserving resource/storage retries precede success; the earlier 2 GiB stop and tmpfs publication failure are not logic passes.

The prevention fixture checks fourteen fixed-table/distance boundaries and empty/missing lookup nil behavior. The final fixture returns nonzero at the first false check; compile, manual link, real execution and complete stdout are checked against the pinned producer Hello runtime and real entry object. Receipt: `/mnt/c/Temp/simple-manual-huffman-4cca-20261011/semantic-controls-nonzero/evidence.json`. No general compression/roundtrip qualification is claimed. Full compiler/lib/MCP integration gates are unavailable with this diagnostic producer and remain pending.

Bitstream remains independently broken: see native_huffman_bitstream_nested_array_abi_2026_10_11.md. Do not infer that return annotations repair nested array ABI.

**Revalidated 2026-11-02: still plausible because OPEN (P1); tagged application-source workaround, compiler type inference unresolved; no merged fix commit with a passing regression is cited in this doc.**

## Lane note 2026-11-03 (wl01 lane)
Landed tagged source workaround (typed params on huffman_lookup, src/lib/nogc_sync_mut/compression/gzip/huffman.spl:17-18, tag bug=native_huffman_untyped_return_guard_2026_10_11). Compiler-side fix (untyped iterable params typed i64 by MIR) remains open: needs a native-build producer to qualify (no native-build available on the Windows seed lane; the interpreter gzip spec does not exercise native MIR). Row stays open.

## Lane note 2026-11-03 (comp-huffret)
Typed the remaining untyped params (`code`/`length`/`distance`: i64) of deflate_length_decode_info, deflate_distance_decode_info, deflate_length_extra, deflate_distance_extra in huffman.spl; all functions now have explicit param and return types. Status: fix-implemented-verification-pending. Verify: native-build test/fixtures/compiler/huffman_workaround_probe/main.spl with a native producer (not available on the Windows seed lane). Compiler-side inference fix remains out of scope.
