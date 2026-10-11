# Item 6 gzip MIR unblock and LLVM package failure

Status: focused MIR unblock; executable verification OPEN.

The admitted pure-Simple Stage 2 compiler (SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`) ran with `SIMPLE_NO_STUB_FALLBACK=1` and `SIMPLE_LIB=src`:

`compile src/lib/nogc_sync_mut/compression/gzip/inflate.spl --format=smf --output build/mini_builds/item56_gzip_huffman_native_mir_20261011.smf`

The Huffman length validation loop now uses indexed iteration. Its three-module focused closure completed HIR, monomorphization, MIR (3/3), borrow checking, MIR optimization, and AOP. The previous native MIR `for-in over non-array iterables` error at `inflate.spl:218` was absent.

The same run then failed at SMF package creation: `unsupported LLVM value conversion from ptr to void` in `lib.nogc_sync_mut.compression.gzip.inflate._inflate_block_dynamic_bounded`, value `%l100`. No SMF output was produced. The HIR log also warns of erased `Any` escaping around line 268, which may be related but is not proven as the cause. Log: `build/mini_builds/item56_gzip_huffman_native_mir_20261011.log`.

This focused result removes one MIR obstacle in the Item 6 dependency closure. It does not prove the 122-module SCV snapshot compile, ordinary CLI V3 publication, a warm native build, or matched p95/RSS cohorts.

## Typed return follow-up

Two further bounded runs used the same admitted compiler and three-module closure. Declaring `_inflate_block_dynamic_bounded` as `[Any]` moved the packaging failure to `huffman_build` (`%l140`). Declaring `huffman_build` as `[[i64]]` with typed table arrays moved it to `_inflate_block_stored_bounded` (`%l55`). Both runs completed MIR and AOP; neither produced an SMF. The logs are `build/mini_builds/item56_gzip_typed_return_cycle2_20261011.log` and `build/mini_builds/item56_gzip_typed_tables_cycle3_20261011.log`. These results identify return ABI inference across multiple untyped gzip helpers as the next root-cause investigation. The three-cycle limit is exhausted; no full compile or runtime behavior is qualified.
