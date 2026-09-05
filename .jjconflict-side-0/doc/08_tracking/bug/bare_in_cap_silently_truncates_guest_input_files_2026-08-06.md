# Ring-3 exec input open(): hardcoded 1 MiB `BARE_IN_CAP` silently truncated any guest-read file larger than 1 MiB

Date: 2026-08-06
Lane: B1 (in-guest clang compile of `llvm/lib/Support/DivisionByConstantInfo.cpp`), toolchain self-host bootstrap plan
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## 1. Symptom

Staging `build/os/b1_witness/TU1.I` (1,164,308 bytes, the preprocessed
`DivisionByConstantInfo.cpp` translation unit) into the guest FAT32 image and
compiling it in-guest via `clang -cc1` would have silently produced a
corrupted/truncated object file — or a spurious parse error whose root cause
would have looked like a preprocessing/clang-flags problem, not a filesystem
bug — with **no error signal anywhere in the path**.

## 2. Root cause

`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`, ring-3
`_bare_exec_handle()` syscall dispatcher, case 30 (`open`), the INPUT-file
branch (guest `open()` on a non-`O_CREAT` path, e.g. clang's `-cc1` opening
its translation unit). Before the fix:

```c
#define BARE_IN_CAP (1u << 20)   /* 1 MiB input (hello.c is tiny) */
static uint8_t _bare_in_buf[BARE_IN_CAP];
...
int rc = fat32_read_file(pbuf, _bare_in_buf, BARE_IN_CAP, &br);
```

`fat32_read_file()` itself (same file, ~line 2821) is not buggy in isolation
— it honors whatever `max_size` its caller passes:

```c
uint32_t to_read = file_size < max_size ? file_size : max_size;   /* line 2826 */
```

The defect is that its ONLY caller on this path handed it a **hardcoded 1
MiB** `max_size` regardless of the real file size, and then treated `rc == 0`
as unconditional success — there is no way for the caller to learn that
`to_read < file_size`. Any guest-opened input file over 1 MiB (TU1.I at
1.16 MB; a real clang binary at ~127 MB would hit the identical wall) would
be silently cut to exactly 1,048,576 bytes with `rc == 0` and no diagnostic.
`_bare_in_buf` was also a single shared static buffer for ALL simultaneous
input opens (the `_bare_in_taken` flag was set but never actually checked —
a separate latent issue, out of scope here since a single-TU `clang -cc1`
invocation opens one source at a time).

## 3. Fix

Same file, case 30 input-open branch: probe the REAL file size first via
`fat32_find_file()` (which the FAT32 driver already exposes and which
`fat32_read_file()` itself calls internally to get `file_size`), then
allocate a buffer sized to exactly that (via the existing `nvme_alloc_aligned`
bump allocator, which backs a 1 GiB freestanding heap — see
`BAREMETAL_HEAP_SIZE` at line ~596 — so a 1.16 MB or even 127 MB allocation is
well within budget). `fat32_read_file()` is now always called with
`max_size == psize`, so its internal `to_read = min(file_size, max_size)`
cap can never bite. Belt-and-suspenders: if the read still comes back short
(`br < psize`, unreachable in practice but never assumed), the open fails
loudly with `-EIO` instead of silently handing back partial data. A file
larger than a 512 MiB sanity ceiling (`BARE_IN_MAX`, guards against a corrupt
directory entry) is refused with `-EFBIG`, also explicit, never silent.

The removed `BARE_IN_CAP` constant and its `_bare_in_buf` static array are
gone entirely (no longer used anywhere — `grep` confirms zero remaining
references) rather than left as dead/misleading code.

Diff location: `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`,
around what is now line ~16660 (constants) and ~16875-16960 (open handler).

## 4. Sabotage-verification proof

No existing test pinned the old 1 MiB behavior (`grep -rn BARE_IN_CAP
test/ doc/` was empty before this fix — nothing to update).

A standalone host-side harness
(`sabotage_bare_in_proof.c`, kept in scratch, not committed — the file
mocks `fat32_find_file`/`fat32_read_file` with the driver's REAL documented
semantics: `to_read = file_size < max_size ? file_size : max_size`)
replicates both the OLD control flow (fixed 1 MiB static buffer, no size
probe) and the NEW control flow (probe + exact alloc + fail-loud) against a
1,164,308-byte fixture (the real TU1.I size) filled with a non-trivial byte
pattern:

```
[OLD] rc=0 size=1048576 (file=1164308) -> SILENTLY TRUNCATED (confirms pre-fix defect)
[NEW] rc=0 size=1164308 (file=1164308) -> FULL READ
[NEW] byte-compare OK: 1164308/1164308 bytes identical
[SABOTAGE] reverting to hardcoded cap => new-style assertion FAILS as expected (test has teeth)
=== OVERALL: PASS ===
```

This confirms: (a) the OLD shape reproduces the documented defect exactly,
(b) the NEW shape reads the full file byte-for-byte, and (c) re-injecting the
old hardcoded cap into the NEW-style assertion flips it to FAIL — the proof
is not vacuous.

## 5. What was NOT completed this session — B1 in-guest run

Building and booting the actual OVMF-based end-to-end harness (stage
`/TU1.I` into a real FAT32 image, boot under real OVMF pflash firmware —
never `-kernel`, per `.claude/rules/board-runnable.md` — spawn `clang -cc1`
in ring 3 through this exact fixed `open()` path, retrieve the resulting
`.o` over the existing base64-serial-dump mechanism, sha256-compare against
the host reference `f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4`)
was **not attempted** this session. No committed script assembles that exact
pipeline yet (the closest existing harnesses,
`scripts/os/build_clang_stream_ring3.shs` and
`scripts/os/build_fsexec_prod_ring3.shs`, target a different code path — the
boot-time streaming ELF loader / production ring-3 spawn — not a guest
process making its own `open()`/`read()` syscalls against a `clang -cc1`
input file, and the former also still boots via `-kernel`, which is itself a
separate open item against the board-runnable rule). Standing up that harness
(FAT32 staging of `TU1.I` + OVMF boot + `clang -cc1` ring-3 spawn wired to
the exact flags in `build/os/b1_witness/{b1,b2}.sh` + serial retrieval +
sha256 compare) is the remaining B1 work and should be picked up as a
follow-up lane. The fix in this doc removes the specific blocker that would
have corrupted that run; it does not itself constitute a B1 pass.
