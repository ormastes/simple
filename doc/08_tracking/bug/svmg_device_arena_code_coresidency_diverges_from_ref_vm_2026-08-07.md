# SVM-G device single-buffer code/data co-residency diverges from ref_vm's separate code array
## Resolved 2026-11-25 — owner-chosen option 2 fully landed (see addendum below)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: resolved 2026-11-25 (owner chose option 2 on 2026-11-04; the vector
  retarget half of that resolution only landed 2026-11-25 — see addendum)
- Found: 2026-08-07, Task C3 (vulkan_vm executor), while running the D3
  conformance vectors against the real `svmg_vulkan_kernel.spv` shader on a
  live Vulkan device.
- Also applies to: Task B3's `svmg_cuda_kernel.ptx` (never verified against
  D3 on real hardware before this task -- see below).

## Symptom

`test/fixtures/svmg/conformance_vectors.spl`'s `mem_store_load_byte` vector
(`PUSHI 50; PUSHI 200; STORE8; PUSHI 1; PUSHI 50; LOAD8; SYS_RESULT; HALT
0`) expects `SYS_RESULT` to record `(passed: 1, value: 200)`. On the real
Vulkan device it instead records `(passed: 13107201, value: 200)` --
`13107201 = 1 | (200 << 16)`.

## Root cause

`src/lib/common/svmg/ref_vm.spl`'s `SvmgVm` keeps `code: [u8]` and
`arena: [u8]` as two **separate** host arrays; `SvmgVm.step` fetches every
opcode via `_u8_at(self.code, pc)`, never through `self.arena`. A `STORE8`
into the arena's DATA region can therefore never perturb instruction fetch,
even though `build_arena` also copies `code` into `arena[code_off..]` for
SGP-blob bookkeeping -- that copy is never read back during execution.

Both device kernels (`svmg_cuda_kernel.ptx`, and this task's
`svmg_vulkan_kernel.spvasm`) have only **one** buffer -- the single GMB-1
arena a real device receives one pointer to -- and fetch every opcode via
`arena[code_off + pc]` directly (see each kernel's own header comment,
which documents this as intentional: `code_off`/`code_len` locate code
*within* the single arena per the SGP wire format's literal meaning,
`src/lib/common/svmg/sgp.spl`).

`mem_store_load_byte`'s program stores to absolute arena offset 50, which
falls inside that exact program's own code footprint (`code_off=36`,
`code_len=25` -> code occupies arena bytes `[36,61)`) -- specifically byte 2
of the very next instruction's (`PUSHI 1`) 4-byte immediate operand (arena
bytes 47..51). On a real single-buffer device this is genuine (if
accidental, on the vector author's part) self-modifying code: byte 50
becomes 200 before the `PUSHI 1` fetch reads its operand, so the pushed
value is `1 | (200 << 16) = 13107201`, not `1`.

`mem_store_load_word` (the STORE32/LOAD32 sibling vector) does not exhibit
this because its STORE32 target (absolute offset 100) happens to land
outside that program's own (smaller) code footprint -- so this divergence
was never caught by inspection, and no test drove either device kernel
against the D3 table before this task.

## Verified not a device/shader bug

Ruled out by: (1) rewriting `svmg_vulkan_kernel.spvasm`'s byte-write helper
twice (once call-based, once fully inlined with `Volatile` loads/stores) --
byte-identical corrupted result both times; (2) hand-tracing the exact
arena byte layout for this program and confirming byte 50 lands inside the
`PUSHI 1` operand; (3) sabotage-probe on an unrelated opcode (`ADD`->`SUB`)
confirmed the shader's assertions are live and would catch a real defect
(see the C3 task report).

## Which side is "correct"

Arguably the device kernels (single buffer) are the behavior a real SVM-G
deployment will actually exhibit -- `ref_vm.spl`'s two-array split is a
host-side convenience that happens to mask self-modifying-code side
effects the wire format doesn't actually prevent. This is a real semantic
gap in the D2/D3 host-side conformance authority, not something either
device kernel should "fix" by faking a result ref_vm didn't actually
produce on real single-buffer hardware.

## Unblock condition (pick one)

1. Decide the design intentionally forbids code/data co-residency effects
   (i.e. code is conceptually read-only / snapshotted at launch) and fix
   `ref_vm.build_arena`/`SvmgVm` to snapshot `code` from `arena[code_off..]`
   at each fetch (making the host match the device), OR
2. Decide self-modifying code is out of scope / undefined behavior and
   retire or relabel `mem_store_load_byte` to pick a STORE8 target outside
   its own code footprint (matching `mem_store_load_word`'s existing,
   accidentally-safe choice), OR
3. Accept the divergence as documented device behavior and leave
   `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl`'s
   explicit per-vector exclusion (and `svmg_cuda_kernel.ptx`'s conformance
   suite, once B3 gets one) in place permanently.

## Related

- `src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl` (Task C3)
- `src/lib/gc_async_mut/gpu_lane/svmg_vulkan_kernel.spvasm` (Task C3)
- `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl` (Task C3)
- `src/lib/gc_async_mut/gpu_lane/svmg_cuda_kernel.ptx` (Task B3 -- no device
  conformance spec exists yet; filed separately as a gap below)
- `src/lib/common/svmg/ref_vm.spl` (Task D2)

## Triage 2026-09-13
Reconfirmed: documented divergence, not blocking, per this record. Needs a
live Vulkan device to re-verify meaningfully; not attempted here. Left as
open/documented, no code change attempted.
## Re-check 2026-09-13 (BUGFIX-12 shard 22)

`src/lib/common/svmg/ref_vm.spl` still present and unchanged in shape (still
keeps a separate `code`/`arena` split per the description above). This needs
an explicit design decision among the three unblock options (snapshot
semantics, retire/relabel the vector, or accept permanently) — not a local
code fix — so it stays out of scope for a shard triage pass. No change made.
Leaving OPEN as documented ("not blocking").


## Resolution 2026-11-04 (owner chose option 2)

Retargeted the STORE8/LOAD8 address of `mem_store_load_byte` in
`test/fixtures/svmg/conformance_vectors.spl` from absolute arena offset 50
(inside the program's code footprint `[36,61)`) to 128, clearly in the DATA
region past the code, so ref_vm and the single-buffer device kernels agree
(expected `(passed: 1, value: 200)`). The vector intent is unchanged (store a
byte, load it back). Removed the per-vector exclusion and the "device-correct
self-modified result" check (`13107201`) from the Vulkan, CUDA and Metal
conformance specs. `ref_vm.spl` is unchanged. Device lanes were host-skipped
here, so device agreement is by construction, not observed.

## Addendum 2026-11-25 — retarget had not actually landed; landed now

Audit on `release/1.0.0` found the 2026-11-04 resolution only half-applied:
commit `c2c6c0c45a0` removed the per-vector exclusion and the `13107201`
device-correct check from the Vulkan/CUDA/Metal conformance specs, but
`test/fixtures/svmg/conformance_vectors.spl` still carried the original
`PUSHI 50 ... STORE8 ... PUSHI 50 LOAD8` program (`git log --all -S "PUSHI 128"`
on that file: no hits). With the exclusion gone and the vector unretargeted,
a live single-buffer device would still produce `13107201` and now FAIL the
conformance specs instead of being excluded.

This change applies the retarget the resolution describes:
`mem_store_load_byte` now stores/loads at absolute arena offset 128.

Verification (code inspection; execution environment-blocked):
- `build_arena` (`src/lib/common/svmg/ref_vm.spl:141`) sets
  `code_off = SGP_HEADER_SIZE = 36` (`src/lib/common/svmg/sgp.spl:44`);
  this program's `code_len` is 25, so its code footprint is arena bytes
  `[36,61)`. Offset 128 is past the 61-byte SGP blob (header + code, no
  `data_init`), in the zeroed DATA region — outside the code footprint.
- `ref_vm.spl` keeps `code`/`arena` as separate arrays, so the host-side
  expectation `(passed: 1, value: 200)` is unchanged by the new address;
  the host gate `test/02_integration/svmg/conformance/conformance_suite_spec.spl:214`
  checks the vector by name with unchanged expectations.
- `bin/simple.exe test` cannot run at this HEAD: the pinned seed rejects
  `@representation_boundary` (repo-wide source/binary inconsistency from
  `cfd89933699`), failing in the test runner's own
  `src/app/test_runner_new/test_runner_client.spl:9` before any spec loads.
  Device lanes additionally require live Vulkan/CUDA/Metal hardware. Both
  limits stated; no execution evidence claimed.
