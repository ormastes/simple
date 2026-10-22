# Phase-2 producer has no Cranelift: producer7-cl relinked against an owner=c Rust archive (workaround)

- **Date:** 2026-10-20
- **Status:** open — workaround active (artifact relink, no source change)
- **Workaround tag:** `@workaround bug=p4p2_cranelift_producer7_relink_owner_c_workaround_2026-10-20`
  (in the lane link script `p4-phase2-20261020/producer7-cl/link.sh`)
- **Affected producer:** `producer7-20261020/strict/simple-producer7-strict.exe` (release_phase3 `87b9c74ff39`)
- **Lane:** `C:/dev/simple-bootstrap-storage/p4-phase2-20261020` (Phase-4 tools built by the Phase-2 compiler, llvm + cranelift)

## Defect

The phase-2 producer is linked with the `core-c-bootstrap` runtime bundle. That
bundle carries `runtime_cranelift_bridge_stub.obj`, whose `rt_cranelift_*`
entries are a named trap (abort, `0xC0000409`, PR #3845). Cranelift codegen runs
inside the producer and its native-build workers, so `native-build --backend
cranelift` with producer7 traps in the first codegen module of every tool.
`grep -a cranelift_codegen simple-producer7-strict.exe` finds nothing.

The real fix is a producer built with the runtime-owner switch (PR #3923,
`--runtime-owner=c`), which needs a producer rebuild. Until then the lane uses the
relink below.

## Workaround (artifact only)

1. Cede `simple_native_all.lib` (the Rust archive in
   `p4-goto-end-20261019/native-all-runtime`) against producer7's own core-C
   objects, `build/cache/native-objects-GJVaEQ/core_c_runtime/*.obj` and
   `strict/runtime_core_intrinsics.obj`, with the bridge stub excluded. This uses
   `rt-owner-c-20261019/runtime_owner_cede.exe` from PR #3923.
   Result: `c_objects=27 c_defined=2481 ceded=1782 members=64 comdat_demoted=1722`.
   The result is non-zero, so this is not the `undefined == 0` fail-open case
   found in the #3923 review.
   - This does not use the prepared `rt-owner-c-ordinary` archive. That archive
     was ceded against the *ordinary* composition, but producer7 links the
     `core-c-bootstrap` objects. Ceding against a different C set leaves
     duplicate or undefined names. The first link attempt, with the intrinsics
     object left out of the cede set, failed with
     `duplicate symbol: __simple_intrinsic_bounds_check`.
2. Relink producer7's `strict-link.rsp` with these inputs:
   - the explicit core-C objects (no stub) in place of `simple_runtime.lib`, plus
     the ceded archive;
   - the dynamic CRT: `ucrt.lib msvcrt.lib vcruntime.lib` with
     `/NODEFAULTLIB:libucrt.lib libcmt.lib libvcruntime.lib`. The Rust archive is
     `/MD`. With the static CRT the link fails with
     `undefined symbol: __declspec(dllimport) _stricmp`.
3. Output: `p4-phase2-20261020/producer7-cl/simple-producer7-cl.exe`, size 37,822,976.
   The strict producer is 33,407,488.
   - `grep -a cranelift_codegen` finds 7 hits.
   - `link.map` binds `rt_cranelift_new_module` to `simple_compiler ... cgu.0`
     (the Rust bridge), and contains no `cranelift_bridge_stub`.
   - `--version` prints `simple-bootstrap 1.0.0-rc.1`.

## Known hazards (from the Fable review of #3923)

- producer7-cl uses **pre-review #3923** (`7197c142251`). With owner=c,
  `rt_thread_free` on an unjoined running thread is a use-after-free
  (`runtime_thread.c:644-656`); #3923 is fixing it. producer7's C runtime is even
  older: it predates the #3923 C thread contract. If producer7-cl crashes
  intermittently in threaded codegen, suspect this first.
- The cede tool's own success check is fail-open on `undefined == 0`. Always check
  that its `ceded=`/`members=` counts are > 0.

## Retirement

Rebuild the phase-2/phase-3 producer from a tree that contains the fixed #3923,
with `--runtime-owner=c`. Then `grep -a cranelift_codegen` on the deployed
producer must find the bridge, and this relink is deleted.
