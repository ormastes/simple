# Default core-C AVX512 boundary and fallback parity

## Scope

Base: `669d900b477af5cb15cad14a91410e958d739a9a`. The default C dispatcher no longer embeds bitmap AND, glyph-mask or coverage AVX512 kernels. It retains public API signatures, scalar and AVX2 behavior, the public OS-state feature query, and all other runtime source inventories. Separately loaded vector-provider sources are unchanged. They implement their existing packed bitmap/HTTP wire operations, not these SplArray blend APIs.

This is not full application/provider integration, nor a claim that all default compiler images lack AVX512. Rust native-all has independent static AVX512 implementations. No live compiler, app, root cache or source freeze was changed.

Removing dispatch exposed a genuine parity bug: the old scalar mask path forced alpha opaque when mask coverage was zero. The existing AVX512 route preserved the original pixel. The fallback now preserves the entire original slot at zero coverage for both packed bytes and integer-slot masks.

## Actual evidence

Retained directory: `/var/tmp/item5-default-avx512-boundary-20261005`.

- Actual public API harness: eight lengths (1,3,4,7,8,9,17,65), 1,650 assertions. Bitmap high bits, complementary/self operands, fresh outputs, rejected zero limit; both mask representations with zero/1/127/254/255 coverage, offsets and nonopaque destination alpha; signed/zero/positive coverage; preserved destination, right operand and boxed-mask source spans including adjacent elements (packed-mask and coverage inputs are not independently snapshot-asserted). No copied runtime kernel or fake provider.
- Identical harness against pre-change runtime: exit 1, line 47/check 234. Patched runtime: exit 0, all 1,650 checks. This does not claim arbitrary malformed arrays or output guard pages.
- Patched executable under `qemu-x86_64 -cpu Nehalem`: all 1,650 checks pass, exercising baseline without AVX2.
- Separate retained public bitmap dispatch harness under GDB: 34 word checks pass; actual `db_bitmap_and_avx2` entered three times. Existing GDB fixture now expresses that preserved route.
- Complete dispatcher object and linked executable disassembly contain no ZMM/opmask instructions; removed symbols absent, AVX2 symbol retained. The three affected public APIs are all used. Object-level inspection independently excludes garbage-collection-manufactured absence.

Same flags before/after: Clang `-std=gnu11 -O2 -g1 -march=x86-64 -ffunction-sections -fdata-sections -DSIMPLE_CORE_C_STANDALONE=1`, shared production runtime_native object; executable link `--gc-sections -lpthread -ldl -lm`. Exact commands retained in `D:/dev/simple/build/review/item5-default-boundary-proof.sh` and `item5-default-boundary-routes.sh`.

| Measurement | Before | After |
|---|---:|---:|
| Dispatcher object text (`size`) | 52615 | 48718 |
| Public harness ELF text (`size`) | 27683 | 23539 |
| Executable PT_LOAD FileSiz/MemSiz | 0x44ed | 0x378d |
| Executable segment 4KiB page span | 5 | 4 |

This is one isolated harness, not an entire compiler ELF or measured RSS reduction. Full default compiler inspection remains required after its own build.

Tested dispatcher SHA256: `6f073e5e3cd13e450d90564f117a9f9883404287b452cc5f8f80d553b61953cb`.
Tested public oracle SHA256: `4a771b4d1d5dbad2195422e235bc763d3c5c97ab2821bc8a518345a09f9addb0`.
Artifact hashes, complete object symbols/disassembly, ELF segments/sections and run logs are retained in the evidence directory.

## Performance tradeoff

One bounded allocation-inclusive sample per variant processed 4,194,304 words/API. Before/after: bitmap AND 26.038/22.976 ms; packed mask 34.303/36.684 ms (+6.9%); coverage 37.937/39.735 ms (+4.7%). Checksums matched. This single noisy sample establishes no general speed claim; removing wide blend kernels trades possible renderer throughput for default image size. Larger renderer workloads and future admitted blend providers remain separate work. No app/performance acceptance is claimed.

## Maintained check

`sh scripts/check/check-runtime-bitmap-avx512-native.shs` retains its historical filename but now compiles the actual default C public oracle and checks complete-object absence plus AVX2 presence under an enforced watchdog. Unsupported platforms exit 77, never PASS. Its previous forced-static-kernel assertion is intentionally retired, not silently skipped. `check-simd-kernels-vectorized.shs` remains explicitly a Rust-authority tier check. External provider qualification stays in the separate provider checks.

The packaged script was syntax-checked; its unchanged underlying compile/run criterion was already exercised by the retained proof and was not rerun. Release gates and parent review are separate from the native proof above.
## Review follow-up: redundant copy removal

Every scalar mask iteration now assigns its output, including the explicit zero-coverage case. Removed the old whole-span precopy and stale lane-kernel comments. This final source passed one new native and Nehalem run (1,650 assertions each); complete object/executable AVX512 absence and AVX2 presence passed. Retained artifacts use `after-copy-removed` names; original before and first-after artifacts were preserved. The table and dispatcher hash above identify this final source. The unchanged bitmap dispatch's earlier GDB result remains its evidence, not a newly repeated test.

New after-only performance sample: AND 23.331 ms, mask 35.070 ms, coverage 63.531 ms. Compared with retained baseline, mask is +2.2%, coverage +67.5%. The coverage body changed only a comment in this follow-up, and its first-after sample was 39.735 ms; these single samples are noisy but the larger observed cost must not be hidden. No performance recovery or equivalence is claimed. A dedicated stable renderer benchmark/provider plan remains necessary before claiming throughput acceptance.

Independent source/receipt review found no P0/P1. Final follow-up recipe: `D:/dev/simple/build/review/item5-default-boundary-copy-removal.sh`. Final ELF SHA256 `072948c1130304b2d508ebb63056bda4f24ef567bd17747272b260c6c28131e5`.