# Native Huffman bitstream nested-array ABI failure

Status: OPEN (P1).

With producer 4cca9585 and the tagged source workaround, the four-control bitstream fixture compiles and manually links, but the real executable exits SIGSEGV (-11), emits no stdout, and reports rejected invalid array handle value_bits=0x0300000000000000. Receipt: `/mnt/c/Temp/simple-manual-huffman-4cca-20261011/bitstream-controls/evidence.json`. It binds exact generated object, runtime object and real Hello entry hashes.

Minimal fixture: test/fixtures/compiler/huffman_bitstream_array_abi_probe/main.spl, calling bitstream_finish(bitstream_new()). Exact minimal execution receipt: `/mnt/c/Temp/simple-manual-huffman-4cca-20261011/bitstream-minimal/evidence.json`. The minimal fixture actually exits 0 and prints bitstream-empty:ok, but emits the same invalid-array-handle runtime error on stderr; its FAIL_EXECUTION receipt rejects that warning. It does not reproduce SIGSEGV by itself. The broader four-control fixture still crashes when writing/reading bits. Expected behavior includes an empty byte array with no runtime ABI error; neither warning nor crash is accepted.

Cause is unproven. Unannotated bs indexing and a nested byte array inside [Any] are candidate loss/boxing paths. Root triage: `/mnt/c/Temp/simple-manual-huffman-4cca-20261011/root-bitstream-triage.json`. A permanent compiler repair needs independent nested-array and typed-parameter controls. This record does not claim source return annotations fix bitstream behavior.

**Revalidated 2026-11-02: still plausible because OPEN (P1); no merged fix commit with a passing regression is cited in this doc.**

## Lane note 2026-11-03 (wl01 lane)
Not fixed: cause unproven (see above) and bitstream_new/bitstream_finish exist only in the fixture test/fixtures/compiler/huffman_bitstream_array_abi_probe/main.spl:6, not in src/. Blocker: needs a native-build run with ABI/array-handle tracing to locate the nested [Any] byte-array boxing path; unavailable on this host (seed refuses native-build entry-closure, 2 GiB alloc abort per native_build_source_closure_zero_sources_2026-08-17).

## Closed-stale 2026-11-03 (comp-huffabi)
Status: CLOSED-STALE (src side). Evidence on origin/release/1.0.0:
- `git grep bitstream_new -- src/lib/nogc_sync_mut/compression/gzip` has no hits; the `[Any]`-tuple-with-nested-`[u8]` bit writer was removed by 81f33f8e1b6 (fix(gzip): ... O(n^2) bit I/O) and the fixture header states the gzip writer no longer uses this shape (2026-10-18).
- Remaining `[[i64]]` in huffman.spl are typed code tables (`huffman_lookup(codes: [[i64]], ...)` typed by 13c3b792fc4), not the failing bs shape.
- The residual repro (test/fixtures/compiler/huffman_bitstream_array_abi_probe/main.spl) stores `[u8]` inside `[Any]`, which is an error outside `unsafe:` under current policy (Any/erased access), so it is not a supported shape; no compiler change is required.
