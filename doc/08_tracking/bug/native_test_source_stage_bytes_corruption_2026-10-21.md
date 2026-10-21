# Native test source staging writes corrupted bytes (2026-10-21)

## Observed failure

A retained diagnostic stage for `test/01_unit/compiler/borrow/ownership_types_spec.spl` is not a copy of its input. The source is 7,980 bytes, SHA-256 `cf5f004cc8950125fcaacc383fb3bf698958de65825f464d09337ddc1dfb54a7`, and starts with `# @req AC-OWN-03`. The staged `entry.spl` is 4,095 bytes, SHA-256 `4ba7db076fb21c811588da83d8d5878aacf3ff0bea6be6e5988b95f89dfd93a1`; its first 40 bytes are `080000000000002c1f0000000000002c1f000000000000e0aa574a37c90000000000000000000041`. The source prefix does not occur in the staged file. The diagnostic retention receipt is `build/nogc-hardening/failed-native-stage-diagnostic-3/retention-receipt.json`.

## Relevant implementation path

`src/lib/nogc_sync_mut/test_runner/native_test_source_stage.spl:38-59` reads the requested source with `file_read_regular_no_follow_bounded_bytes(source_path, size)` and passes the resulting `[u8]` directly to `file_write_bytes(stage.path, bytes)`. The wrapper in `src/lib/nogc_sync_mut/io/file_ops.spl:187-189` forwards `(path, data)` to `rt_file_write_bytes`; the native provider declares `(path_ptr, path_len, data_ptr, data_len)` in `src/runtime/simple_core/core_fs.spl:556` and writes that span. The staging code contains no text conversion or intentional prefix.

The staged prefix is binary, not Simple source. Its initial little-endian words include `8`, `0x1f2c` (7,980), and another `0x1f2c`, followed by a process-address-looking word. The bounded disassembly diagnosis below establishes an argument-shape mismatch at the byte-array write boundary.

## Confirmed ABI cause

The compiled staging call lowered `file_write_bytes(path, bytes)` to the legacy raw provider `rt_file_write_bytes` with three machine arguments: path pointer/length followed by the packed array handle. Its selected runtime declaration consumes four arguments (path pointer, path length, byte pointer, byte length). The missing fourth argument and treating the array handle as a data pointer explain the metadata-like output and truncation. The producer source passes the complete `[u8]`; the runtime's raw implementation is not the source of the corruption.

The selected runtime authority also exports `rt_file_write_bytes_array`, a two-argument provider that accepts tagged path and byte-array RuntimeValues and extracts the packed bytes before delegating to the raw writer. This is the matching semantic boundary. The pure-Simple lowering repair is restricted to an authoritative local or imported extern declaration of `(text, [u8]) -> bool` with two actual operands. A separate adapted-facade receipt records its defining owner and exact link name; the raw exact-extern ABI registry remains unchanged. It aliases that call to the tagged provider before text boxing/argument expansion; the alias boxes only its text path. Unknown signatures, ordinary local same-name functions, qualified homonyms, and four-argument raw calls retain their existing paths.

The focused source fixture now checks an 8,192-byte roundtrip, beyond the observed 4,095-byte boundary, and a MIR registry spec covers the alias admission and negative cases. These artifacts are source-level evidence only: no build or verification cycle has run for this repair, so successful native output remains unverified.

## Impact and next evidence

Native test-source staging can publish malformed `.spl` input and invalidate native test results. The responsible staged file was moved outside Git source discovery and preserved under `build/nogc-hardening/failed-native-stage-diagnostic-3`; its original generated directory was `test/native-generated--7784378ee1ed`. Do not accept native runner results until a new qualified run proves exact source-to-stage byte equality (length and digest) and the emitted native test executes. No compiler fix, provider fix, or acceptance PASS is established by this incident record.


## Executed qualification: additional provider and boxing defects

The first explicit tagged-facade probe compiled (162.29 seconds, peak RSS 7,023,320 KiB), then failed byte comparison at offset 1. A diagnostic rerun retained the actual 8192-byte output under `/tmp/simple-byte-write-failure-g6aegx0b`; its SHA-256 is `00b4b1ba6522ed93d5bbc194e706e451b895964c8f79add14dfa23fb6228413b` and prefix is `00 08 10 18 20 28 30 38`. C `rt_file_write_bytes_array` masks `rt_array_get` results without decoding generic tagged integer slots. It works only with its packed-byte branch; generic-array runtime qualification is withdrawn. No C or Rust source was changed.

A checked pure-Simple packed-normalization revision compiled in 149.45 seconds (7,066,580 KiB), then returned failure before writing. GDB traced validation count 8192, source basis -1, packed allocation, and a different handle reaching the next basis check (-1). Disassembly proves typed `[u8]` to `Any` conversion allocates a new generic array and loops `rt_array_get`/`rt_array_push`, erasing packed storage. The allocator declaration now returns `Any` directly, retaining the foreign handle; scratch-only cleanup is also added. These source changes remain unexecuted.

Evidence: `build/nogc-hardening/file-bytes-facade-{build,run}-1.log`, `file-bytes-facade-failure-diagnostic-1.json`, `file-bytes-facade-{build,run}-2.log`, `file-bytes-facade-abi-trace-2.log`, `file-bytes-facade-disassembly-2.log`. Existing direct generic-to-array compiler adaptation remains unqualified until its MIR packing implementation is tested. No native byte or source-staging PASS is claimed.

The adapted direct-call MIR path now validates the source array before the writer boundary. It forwards a packed byte array only when the packed-basis length matches the validated count; a non-packed valid array is copied with the checked byte-copy helper into a temporary packed array, then the writer runs synchronously and `rt_array_free` releases only that temporary owner. All validation, allocation-shape, pointer, or copy failures branch to `false` without opening the output. MIR array handles use pointer-shaped LLVM types for the basis/allocation/free calls, with explicit casts only at helpers whose C ABI takes or returns tagged `int64_t` values. This source change has not been built or runtime-qualified.
