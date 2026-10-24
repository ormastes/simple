# Packed byte arrays inherit the generic 100M-element capacity limit

Status: representation-aware repair passed its real C boundary regression.
No passed GNU projection or compiler test is claimed. GNU COFF
owner source round 4/native attempt 2 is held with two attempts remaining; the
byte-capacity cause has its own finite repair budget.

Actual immutable archive:
`C:/dev/simple-gnu-runtime-secure-temp-storage-20261024/runtime-authority/libsimple_native_all.a`,
109,939,334 bytes, SHA256
`dc022e2afae05a4e4be06413ef8ef81a1b46a329da480f4ee8e2cf2d43d6093a`.

The bootstrap-only diagnostic tool was compiled with immutable Rust seed
`5a6a8bec8c8c205b2c4507768acf553b3ef6027018706357350394af09f81622`
and real core-C providers. No Rust seed was rebuilt. First tool build compiled
56 units, exit 0, 6.6s. Its run failed an opaque assertion: native DWORD
`0xC0000409`, collector raw 125, peak 56,380 KiB, quiescent 1. Evidence:
`C:/dev/simple-gnu-coff-owner-storage-20261025/{helper-build,projection}`.

One approved fixture-only change printed real values before existing assertions.
The changed build reused 55 units, compiled one, exit 0, 5.4s. Its run proved all
24 target/ABI cases, nonempty configured paths, all 28 real C objects and actual
archive SHA256. The projection Result then returned `runtime owner: cannot read
archive .../libsimple_native_all.a`, followed by the retained assertion: native
DWORD `0xC0000409`, raw 125, peak 56,412 KiB, quiescent 1. Evidence:
`C:/dev/simple-gnu-coff-owner-storage-20261025/diagnostic2/{helper-build,projection}`.
Full argv, source/input pins, statuses and independent RSS receipts are retained.
Neither run reached rewriting or negative/positive native links. These are not
self-hosted tests or Phase3/4 admission.

The actual C owner explains this refusal:

- `runtime_native.c:336` sets `RT_CORE_ARRAY_MAX_CAP` to **100000000**.
- `rt_core_array_new_fill` at 8314 rejects larger capacity before allocating.
  Packed arrays use `elem_size=1` but inherit the same element-count limit.
- `rt_byte_array_new`/`rt_byte_array_new_len` at 8842/8849 reach that guard.
- `rt_file_read_bytes` at 15929 requests the actual length; allocation returns
  null and line 15931 refuses the read.
- `rt_core_array_ptr` at 2720 and concat at 9601 enforce related bounds; changing
  allocation alone would be incoherent.

109,939,334 exceeds the actual 100,000,000 limit; the RSS guard was not reached.
Small C object reads through the canonical facade already succeeded. Changing
only the extern/facade cannot make this packed allocation legal.

The separate repair must preserve the generic element limit and normal
5,859,375-KiB process-family cap, use checked byte-specific allocation/validation/
concat bounds, and execute a real C boundary regression. No fake archive,
truncated read, duplicate allowance or unbounded streaming framework is implied.
GNU projection is held until the actual runtime profile is fixed and reviewed;
no automatic backend/provider fallback is authorized.

## Implemented repair and actual qualification

The runtime now permits at most 1 GiB of packed bytes; ordinary tagged-slot,
U64-packed and tuple arrays retain the 100,000,000-element limit. The shared
private capacity check guards both `INT64_MAX / element_size` and
`SIZE_MAX / element_size`. Header admission, allocation, concat and reserve
use that contract. Concat receives the byte limit only when both inputs are
packed bytes. Reserve clamps doubling to the valid representation limit;
it cannot successfully publish a capacity its next header check rejects.
Public ABI, structure layout and the process-family RSS guard are unchanged.

Actual regression: `test/runtime/packed_byte_capacity_test.c`. It verified the
archive SHA256 above and read all 109,939,334 bytes, grew the packed array via
push, verified the surviving header, modified byte 100,000,000, checked an
independent copy and full-buffer equality, and checked both halves of a
219,878,668-byte concat. It also rejected mixed output above the generic limit,
ordinary/U64 capacities 100,000,001, byte capacity 1 GiB + 1 and `UINT64_MAX`
without allocating those rejected capacities. Every retained array was freed.

Evidence: `C:/dev/simple-runtime-byte-capacity-storage-20261025/`.
The canonical 28-source C profile reused 25 byte-identical object dependencies
and rebuilt three translation units whose source or local include closure
changed (`runtime_native`, `runtime_core_host_services`, `runtime_legacy_core`).
The latter two carry already-landed upstream changes, not changes in this fix.
Each compile, archive and link exited 0. The real Windows JobObject run returned
raw/native 0, exact `packed-byte-capacity archive/copy/concat passed\n`,
quiescent 1, no job remnants and cleanup not needed. Peak RSS was 407,008 KiB,
peak job commit 557,356 KiB, with configured jobs 24 and the unchanged
5,859,375-KiB guard. No Cargo, runtime-wide rebuild or compiler seed rebuild
was performed. This is runtime boundary evidence, not Phase3/4 qualification.
