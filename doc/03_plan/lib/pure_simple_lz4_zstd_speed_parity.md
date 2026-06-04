# Pure Simple LZ4/Zstd Speed Parity Agent Plan

**Date:** 2026-05-19
**Status:** active plan

## Goal

Replace the current minimal LZ4/Zstd store-path facades with production-grade
pure Simple codec paths, then prove correctness and speed against C library
baselines.

The target is not just "works without C". The completion gate is:

- pure Simple correctness matches the format test corpus;
- pure Simple encode/decode reports `Simple/liblz4 > 1.00x` for the accepted
  LZ4 benchmark profile or has a documented compiler/JIT blocker;
- pure Simple decode reports `Simple/libzstd > 1.00x` for the accepted Zstd
  profile or has a documented compiler/JIT blocker;
- any C library fallback remains optional and explicitly selected.

## Current State

- `src/lib/common/compress/lz4.spl` emits a valid frame through a literal/store
  path and decodes the subset it produces.
- `src/lib/common/compress/zstd.spl` emits and decodes a raw-block framed subset.
- `doc/05_design/common_compression_framework.md` describes a broader intended
  framework than the currently visible source surface; this plan treats source
  behavior as the truth and uses the framework docs as target direction.

## Agent A: LZ4 Correctness Core

**Priority:** P0

### Tasks

- Add pure Simple LZ4 block compressor with hash-chain or hash-table match
  finder, literal run encoding, offset encoding, and match-length extension.
- Add full independent-frame decode for compressed and uncompressed blocks.
- Implement descriptor checksum and optional block/content checksum through the
  shared checksum helpers.
- Preserve raw-block mode as an explicit API; never auto-detect raw blocks
  without a caller hint.
- Keep the existing store path as fallback for tiny or incompressible inputs.

### Correctness Gates

```bash
bin/simple test test/02_integration/core/common_compression_framework_facade_spec.spl --mode=interpreter --clean
bin/simple test test/05_perf/port_algorithms/lz4_pure_simple_parity_spec.spl --mode=interpreter --clean
```

Add the second spec if it is missing. It must include:

- empty payload;
- small text;
- repeated runs;
- incompressible bytes;
- block boundary payload;
- malformed frame/header/block checksum cases.

## Agent B: Zstd Decode Core

**Priority:** P0 after Agent A test harness is reusable

### Tasks

- Implement pure Simple frame parser for single and concatenated frames.
- Implement block decode for raw, RLE, and compressed blocks.
- Implement FSE table construction/decode for literals length, match length,
  and offset codes.
- Implement HUF table decode for literals blocks.
- Implement sequence execution with overlap-safe match copy.
- Keep dictionary-backed frames typed `UnsupportedFeature` until dictionary
  semantics are implemented and benchmarked.

### Correctness Gates

```bash
bin/simple test test/01_unit/os/kernel/loader/zstd_decompress_spec.spl --mode=interpreter --clean
bin/simple test test/05_perf/port_algorithms/zstd_pure_simple_parity_spec.spl --mode=interpreter --clean
```

Add the second spec if it is missing. It must include:

- raw block;
- RLE block;
- compressed literals;
- compressed sequences;
- concatenated frames;
- checksum mismatch;
- dictionary-required rejection.

## Agent C: Zstd Encode Core

**Priority:** P1 after Agent B

### Tasks

- Keep level `1` as the first production encode target.
- Add block splitter and simple match finder.
- Emit raw/RLE blocks when they are smaller or cheaper than compressed blocks.
- Emit FSE/HUF tables only when compression benefit beats fixed overhead.
- Keep high compression levels and dictionaries deferred with typed errors.

### Correctness Gates

```bash
bin/simple test test/05_perf/port_algorithms/zstd_pure_simple_encode_spec.spl --mode=interpreter --clean
```

## Agent D: C Library Speed Comparison

**Priority:** P0, begins with Agent A harness

### Tasks

- Add C reference benchmarks under `test/05_perf/port_algorithms/c_reference/`:
  - `bench_lz4.c` using liblz4 when available;
  - `bench_zstd.c` using libzstd when available.
- Add pure Simple benchmark entries to
  `test/05_perf/port_algorithms/run_port_algorithm_benchmarks.shs`.
- Use the same datasets, iteration windows, warmups, checksum outputs, and
  compressed-size reporting for C and Simple.
- If `liblz4` or `libzstd` is unavailable, print `UNAVAILABLE` and do not mark
  the row passed or failed.
- Record median MB/s and ratio rows in
  `doc/plans/all_cipher_compress_algorithm_gate.md`.

### Datasets

- `text-small`: short HTTP/JSON-like payloads.
- `text-large`: repeated source/doc text.
- `binary-random`: deterministic incompressible bytes.
- `runs`: long repeated bytes and repeated words.
- `mixed`: alternating compressible/incompressible regions.

### Acceptance

Rows must report:

```text
codec, operation, dataset, C MB/s, Simple MB/s, Simple/C, compressed-size-ratio
```

Correctness checksum parity must pass before any speed ratio is counted.

## Agent E: Compression Optimization Plugin

**Priority:** P0 for speed parity, but behavior-preserving only

### Compiler/JIT Hooks

- Add a built-in `CompressionPatternProvider` to the Simple Optimization Plugin
  registry.
- Recognize byte-slice hot loops only when facts prove:
  - typed `[u8]` storage;
  - stable length within the loop;
  - no aliasing between source and destination buffers;
  - bounds checks can be hoisted or folded.
- Lower match-copy loops to a backend-neutral intrinsic shape:
  `copy_match(dst, dst_pos, offset, length)`.
- Lower literal-copy loops to `copy_bytes(dst, dst_pos, src, src_pos, length)`.
- Add bitstream reader combining for Zstd FSE/HUF loops.
- Add static table materialization for Zstd decode tables without the native
  global-cache crash pattern already tracked for CRC32.
- Add target metadata for x86_64, aarch64, arm32, riscv64, and riscv32, but keep
  the semantic pass backend-independent.

### Guardrails

- Plugin rewrites cannot change compressed bytes, decompressed bytes, errors, or
  checksums.
- No benchmark-only source rewrites count as plugin completion.
- A disabled plugin must still pass all correctness specs.
- Dynamic optimization plugins are not required for bootstrap; this provider is
  built-in until the dynamic manifest ABI is proven stable.

### Verification

```bash
SIMPLE_OPT_PROVIDER=compression bin/simple test test/05_perf/port_algorithms/lz4_pure_simple_parity_spec.spl --mode=interpreter --clean
SIMPLE_OPT_PROVIDER=compression bin/simple test test/05_perf/port_algorithms/zstd_pure_simple_parity_spec.spl --mode=interpreter --clean
SIMPLE_LLVM_PROBE=1 SIMPLE_DISASM_PROBE=1 test/05_perf/port_algorithms/run_port_algorithm_benchmarks.shs
```

## Dependency Order

```text
Agent D harness -> Agent A LZ4 -> Agent B Zstd decode -> Agent C Zstd encode
                 -> Agent E compiler/JIT optimization -> final speed gate
```

Agent D starts first because the benchmark contract determines whether later
changes are real performance improvements.

## Documentation Updates Required With Implementation

- Update `doc/05_design/common_compression_framework.md` whenever supported
  codec behavior changes.
- Update `doc/plans/all_cipher_compress_algorithm_gate.md` with measured rows.
- Update `doc/04_architecture/compiler/simple_optimization_plugin.md` when the
  `CompressionPatternProvider` interface or facts become concrete.
- File concrete bugs under `doc/08_tracking/bug/` for any correctness,
  native-code, or benchmark blocker.
