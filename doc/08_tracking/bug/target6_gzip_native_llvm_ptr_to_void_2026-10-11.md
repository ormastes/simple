# Native gzip SMF package rejects ptr-to-void conversion

Status: OPEN.

Reproduce with the admitted pure-Simple Stage 2 compiler and `SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_LIB=src`:

`compile src/lib/nogc_sync_mut/compression/gzip/inflate.spl --format=smf --output build/mini_builds/item56_gzip_huffman_native_mir_20261011.smf`

After the 3-module closure completes MIR and AOP, SMF packaging reports `unsupported LLVM value conversion from ptr to void function=lib.nogc_sync_mut.compression.gzip.inflate._inflate_block_dynamic_bounded value=%l100` and aborts. The output file is absent. HIR warns about `Any` escaping around `inflate.spl:268`; the causal link is unverified.

Expected: a typed source diagnostic or valid LLVM conversion, never a compiler abort. Inspect the `%l100` value owner and the heterogeneous bitstream return shape before changing gzip data representation. See `doc/09_report/compiler/target6_gzip_mir_unblock_llvm_failure_2026-10-11.md` and its retained build log.
