# Item 6 archived native object fixture stops before CAS publication  2026-10-11

Status: OPEN. This is a focused test blocker, not an Item 6 admission PASS.

## Reproduction

In isolated worktree `work/targets-release-20261010` after commit
`a64c73cae9d`, the admitted pure-Simple Stage 2 compiler
(`e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`)
built `test/fixtures/bootstrap_builder/archive_native_object_admission_main.spl`
with LLVM, `simple-core`, entry closure and `SIMPLE_NO_STUB_FALLBACK=1`.
The third bounded build linked 46 modules and produced
`/tmp/simple-target6-archive-fixture-llvm2` (SHA-256
`07f4359a145f1b7eced133db30c703327a5a0649d447e59ba71acf4d862a25a6`).
Running it in the worktree exits 11 and prints `FAIL CAS publication`.
The relative test CAS root and `objects/sha256/1c` directory exist, but
there is no blob. Therefore no archive admission assertion executed.

The first fixture build used Cranelift and stopped on existing imported-global
and module-static support gaps. The second used LLVM and linked all 46 modules,
then failed on an undefined cross-module
`BINARY_OBJECT_CAS_MAX_BYTES` global. The CAS now exposes
`binary_object_cas_read_full` so the cap stays inside its defining module;
the third build linked successfully. The remaining failure occurs inside
`binary_object_cas_put` or its filesystem primitives. It is not yet
attributed to temp-directory creation, byte writing, publish-noreplace, or
readback. The three-cycle verification limit has been reached.

## Next proof

Instrument each CAS publication stage with a typed result or run one
absolute-root fixture in a fresh scoped session, then require a real
publish/readback and all four fixture assertions to pass. Do not treat the
successful link alone as archive admission evidence. Run the full package
route and paired warm time/RSS cohorts separately.

## 2026-10-11 staged-byte ABI investigation

The admitted Stage2 LLVM fixture still exits 11 (`FAIL CAS publication`) before publishing the first eight-byte ELF object. `strace` shows the old `file_write_bytes` call writes 255 bytes of packed-array metadata, then CAS readback rejects the SHA-256 mismatch. The intended object is `7f 45 4c 46 01 02 03 04` and its digest is `1ce1805693fc7e6df020e40f78385981789a078c681dbbcbd1551be1c3939a3e`.

Three bounded write-path probes were built and run in the isolated worktree:

- `rt_bytes_to_text([u8])` plus positioned text write emitted only `f8 03` (two bytes), then CAS rejected the object.
- Existing `rt_file_write_bytes_array` returned before opening the staged file.
- An explicit 1 MiB raw-buffer SOSIX/C writer also returned before opening the staged file.

Trace artifacts: `/tmp/simple-target6-cas-read.trace`, `/tmp/simple-target6-cas-sosix-trace2`, `/tmp/simple-target6-cas-array-trace`, and `/tmp/simple-target6-cas-raw-trace`. Build logs are `/tmp/simple-target6-cas-sosix-fixture-build-20261011.log`, `/tmp/simple-target6-cas-array-fixture-build-20261011.log`, and `/tmp/simple-target6-cas-raw-fixture-build-20261011.log`. The final write-path probe was reverted after the third failed fixture cycle; no writer change is qualified or published. Next investigation should inspect generated LLVM call operands and the runtime argument decoding before another implementation attempt. The CAS publication gate and Item 6 remain open.

## 2026-10-11 native resolution

Generated AArch64 disassembly exposed the path ABI mismatch: the compiler passed a C string through `rt_interp_cstr`, while the first raw writer expected tagged text. The corrected SOSIX/C boundary and binary/chunk fixture now pass. See the [native repair report](../../09_report/compiler/target6_archive_native_cas_sosix_2026-10-11.md). The interpreter/SPipe and production gates remain open.
The final SOSIX alias routing also passed a no-stub native rebuild and fresh-root executable fixture; details and limits are in the linked repair report.
