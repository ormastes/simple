# Default Rust runtime excludes embedded AVX512 kernels

Status: scoped runtime verification passed; not full native-all/compiler, Phase2 app, or dynamic-provider qualification. Source base0cc179e4a9c (release); before archive sourcecdfbe1e has identical compiler_rust/hosted-runtime tree. Five runtime owners remove19 private AVX512 target-feature bodies: byte2, numeric12, primitive-u8sort1, UTF8/ASCII4. Default requests select existing guarded AVX2/scalar. Host capability queries and public function signatures remain; public const primitive-sort dispatch_for_tier retains its request descriptor, while actual sort reports the CPU-admitted dispatch family. This does not claim every type-specific operation vectorizes. Numeric cache keys use the narrowed tier to avoid repeated provider resolution.

No Cargo feature silently restores static kernels. Compatibility helper names containing avx512 now delegate to the existing narrower implementation. Existing dynamic bitmap/HTTP providers remain separate; their64/24byte SIMDKER1 wire covers AND/OR-u32, find-byte and find-CRLF only. General substring/rfind/split, numeric, sort and UTF8 dynamic adapters remain unimplemented. compiler/src/interpreter_extern/simd.rs has separate static blend/bitmap/find AVX512 owners; this change does not remove those or change their vectorization guard.

## Actual evidence

Artifacts: /var/tmp/item5-rust-default-wide-20261006/{before,after}. Final sources pinned in after/sources.sha256. Finite watchdog receipt /var/tmp/item5-rust-default-wide-qualify.rss.env: exit0, peak1125800KiB, cap2097152KiB, quiescent1. Initial immutable compile receipt is /var/tmp/item5-rust-default-wide-build.rss.env; after terminal, numeric cache normalization and formatting preceded the final qualification.

- Focused Rust unit ELF:47PASS,0failed/ignored. Byte, numeric, malformedUTF8, primitive classification/order, wide-request provider and array-sort cases. Public const usage and actual narrowed sort reporting asserted separately.
- Whole libsimple_runtime.a disassembly, before linker GC: before171 runtime-owned ZMM/opmask instruction rows; after1,394,907 disassembly lines contain0 EVEX/ZMM/opmask rows, both runtime-owned and dependency members. This proves the built archive's instruction boundary, not all compiler/native-all images. Analysis script retained at D:/dev/simple/build/review/item5-runtime-archive-isa.py; complete matching rows and JSON under each artifact directory.
- Public C ABI oracle tests real string find, UTF8 count, f64 dot and primitive u8 sort; same C source and flags link both archives. Native before/after and QEMU Nehalem PASS. Requested wide numeric dispatch reports3 before,2 after on the host,0 under Nehalem. No provider DSO is used by this fixture.
- Same-profile linked probe text737963 ->725908 bytes (-12055). Executable LOAD size0x7ecad ->0x7ce7d (-7728bytes),127 ->125 pages of4KiB. LOAD and text measurements include the probe and runtime dependencies; not whole compiler image savings.

Hashes: after archive0cbab17d784e06f9efa1683727f2a23e424b99e382e60c379f9f75ef703d37c9; after unit ELF81760a18026013f83a0118ef737b57258fc6a5b80c8e858e3d4d860b2fb3ea9b; before public ELF0cc388e7b67c0b6438535d2928d51f2f39bf008141e21b31a91036b7199b6bca; after public ELF5ee39a61784c6a0a0ab07f7b1259059e675e21803db1ff9f1d63eb442d1fc1d9.

## Performance tradeoff and remaining work

One process per artifact,3warmups then30samples, medians below. Setup/reset and sort verification are outside timed sort; other timed loops include result assertions. Each string/UTF8/dot sample performs16calls; sort performs one4096element call. Opt1 test profile is diagnostic evidence, not release-profile or app performance. Concurrent system activity and process ordering are not controlled statistical experiments.

| Public API work | Before | After | Change |
|---|---:|---:|---:|
| Find last byte in1MiB,16calls |7.703ms|7.756ms|+0.7%|
| Count ASCII UTF8 in1MiB,16calls |0.353ms|0.515ms|+45.9%|
| Dot4096f64,16calls |11.822ms|10.657ms|-9.9%|
| Sort4096u8 values |29.148us|27.842us|-4.5%|

**Open performance defect/tradeoff:** default UTF8 ASCII scanning is45.9% slower in this measured workload after narrowing AVX512 to AVX2. Performance equivalence is not accepted. A future authenticated optional UTF8 provider must preserve malformed-input/count/invalid-offset semantics and recover measured throughput without reintroducing wide code into the default archive. Its opcode/interface design is still missing; existing byte/CRLF capability cannot claim UTF8 support. AVX512 DB/web and Simple CUDA application qualification remain separate unfinished work.

## Reproduction

Use isolated targets and identical flags for both source revisions. The retained scripts under D:/dev/simple/build/review are item5-rust-default-wide-build.sh, item5-rust-default-wide-qualify.sh and item5-runtime-archive-isa.py. C oracle source is src/compiler_rust/runtime/tests/default_simd_boundary_public.c. Its optional --smoke reduces samples for future diagnostics; actual retained Nehalem run used the full30sample mode.

From src/compiler_rust: cargo test --locked --offline --target x86_64-unknown-linux-gnu -p simple-runtime --lib --no-run. Run emitted unit ELF with filters value::byte_kernels:: value::utf8_kernels:: value::numeric_kernels:: value::primitive_sort:: value::collections::avx512_provider_dispatch_tests:: test_array_sort --test-threads=1. Build archives with cargo build --locked --offline --profile test --target x86_64-unknown-linux-gnu -p simple-runtime --lib. One Cargo job; no extra RUSTFLAGS; repository .cargo/config.toml applies. Native C command: clang -O2 -march=x86-64 -ffunction-sections -fdata-sections default_simd_boundary_public.c libsimple_runtime.a -Wl,--gc-sections -ldl -lpthread -lm -o public-probe. Run with SIMPLE_SIMD_TIER=x86_64_avx512; QEMU command qemu-x86_64 -cpu Nehalem public-probe. Do not reuse a producer cache under a false identity.

Independent source review found noP0/P1 after const API and numeric cache corrections. Broader Simple compiler/lib/MCP/LSP checks are unrun: available new Phase2 Hello attempts hit their resource cap, and the Rust seed is not substituted for application qualification. Local commit gates are recorded separately by the landing owner.
