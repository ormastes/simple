# native-build --entry-closure collects zero source files for an existing entry (blocks CUDA/Vulkan parity probe)

- **Date:** 2026-08-19
- **Status:** SUPERSEDED (triage 2026-11-11, lane boot21; first triaged 2026-11-10 lane boot5) — collector diagnostic rewritten at `driver_source_pipeline_loading.spl:1004` (PR #7597 `9e7e7a526edb`, ancestor of HEAD `d552f63f67f8`) directly answering this record's complaint (see 2026-11-11 addendum below)
- **Severity:** medium — blocks `check-processing-cuda-fill-native.shs` and `check-processing-cuda-vulkan-native-parity.shs` (probe-binary-missing)

## Repro
The documented recipe
(`doc/06_spec/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.md`):

```sh
cd /mnt/data/worktrees/render-harden
bin/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test/processing_cuda_fill_probe.spl \
  --strip --output build/simpleos_gpu_host/cuda_fill_native/processing_cuda_fill_probe
```

fails with:

```
error: native-build entry 'src/app/test/processing_cuda_fill_probe.spl' collected zero source files:
--entry takes a path to a .spl file ... resolved relative to the current working directory
```

The file EXISTS at that path (verified with `ls`), and an absolute `--entry`
path fails identically, so the error message's diagnosis (bad path / module
path) is wrong — entry-closure collection itself returns an empty set. Binary:
`bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, 2026-08-18 deploy).

## Impact
The parity probe binary can no longer be produced, so the "cuda offload with
vulkan" parity lane reports `processing_cuda_fill_native_status=blocked
reason=probe-binary-missing`. CUDA itself is healthy on this host:
`check-cuda-generated-2d-readback.shs` PASSes (64 device pixels, 0 mismatch)
and `check-cuda-dlopen-fallback.shs` PASSes.

## Next step
Debug the entry-closure collector in the native-build path (seed CLI) or
regenerate the probe with a stage binary once bootstrap redeploy is unblocked.

## 2026-11-10 P3-boot5 triage (row 39) — SUPERSEDED

Premise outdated, corroborating the bugdb close already recorded in
`doc/08_tracking/bug/db/native_build_entry_closure_collects_zero_files_cuda_fill_probe_2026-08-19.sdn`
(2026-11-09). The recorded error text is gone: the collector's message at
`src/compiler/80.driver/driver_source_pipeline_loading.spl:1004` now reads
"collected zero source files: the entry must be a path to a .spl file ... not a
module path ..., and the path is resolved relative to the current working
directory" — directly answering this record's complaint that the diagnosis was
wrong (message rewrite landed via PR #7597 merge `9e7e7a526edb`, 2026-11-07).
Per the 2026-11-09 note, the documented recipe now passes entry collection on
seed and proceeds to an unrelated parse error. A full re-run of the CUDA probe
recipe is host-heavy (Linux CUDA host) and was not repeated from this Windows
lane.


## 2026-11-11 P3-boot21 triage — SUPERSEDED (header flip)

Fresh re-verification of the 2026-11-10 boot5 disposition (not flipped then),
at HEAD `d552f63f67f8`:

- `git merge-base --is-ancestor 9e7e7a526edb HEAD`: ANCESTOR — PR #7597 is in
  this tree.
- The collector diagnostic at
  `src/compiler/80.driver/driver_source_pipeline_loading.spl:1004` now reads
  "collected zero source files: the entry must be a path to a .spl file (e.g.
  'dir/main.spl'), not a module path (e.g. 'dir.main'), and the path is
  resolved relative to the current working directory" — directly answering
  this record's complaint that the error message's diagnosis was wrong.

Per the 2026-11-09 bugdb close
(`doc/08_tracking/bug/db/native_build_entry_closure_collects_zero_files_cuda_fill_probe_2026-08-19.sdn`),
the documented recipe passes entry collection on the seed and proceeds to an
unrelated parse error. A full re-run of the CUDA probe recipe is host-heavy
(Linux CUDA host) and was not repeated from this Windows lane. No code change
this lane; header flipped to match the verified disposition.

## 2026-11-12 P3 fix-runpath-gpu lane — re-verified, aggregate DB row synced to closed

Static re-verification at this lane's pinned HEAD `7a06b4aafd5` (no
working compiler on this host, so no live re-run of the CUDA probe recipe):

- `git merge-base --is-ancestor 9e7e7a526edb HEAD` — ANCESTOR (PR #7597 in
  this tree).
- `src/compiler/80.driver/driver_source_pipeline_loading.spl` (around
  line 1004) carries the fail-closed zero-source diagnostic naming the true
  cause ("the entry must be a path to a .spl file ... not a module path ...
  resolved relative to the current working directory") plus the ROOT FIX
  that loads the entry's transitive import closure — exactly the defect and
  wrong-diagnosis complaint this record documents.
- The per-bug db file
  (`doc/08_tracking/bug/db/native_build_entry_closure_collects_zero_files_cuda_fill_probe_2026-08-19.sdn`)
  already recorded `closed` on 2026-11-09; only the aggregate
  `bug_db.sdn` row was still `open`. This lane synced the aggregate row to
  `closed` with an updated title and `updated_at=2026-11-12`.

No code change this lane (nothing left to fix in scope). A full re-run of
the CUDA fill native probe recipe remains pending a Linux CUDA host.

Status: CLOSED (superseded upstream; bookkeeping synced).

## 2026-11-22 live re-run on a Linux CUDA host (lane work/cuda-compiler-bugs) — CLOSED, verified

Host Linux aarch64, NVIDIA GB10, base `origin/release/1.0.0` `3c2e4556b6d`.
Producer: integ25 Stage 2 admitted native-build (sha256
`ef46f0d2ab4274c4550530851db407bf9bad7f21bfabd50f9b56e87e77fd58d6`), runtime
`stage2-runtime-authority`, under `systemd-run --user --scope -p MemoryMax=8G`.

Documented recipe (`--source src/compiler --source src/app --source src/lib
--entry-closure --entry src/app/test/processing_cuda_fill_probe.spl --strip`):

- Run 1 (no `--runtime-path`): entry closure collected **112 modules**, parse ->
  HIR -> native_compile all ran. Link failed on undefined `rt_cuda_*` because the
  default runtime objects lack the CUDA surface. The zero-files defect does not
  reproduce.
- Run 2 (`--runtime-path <stage2-runtime-authority>`): build rc=0, binary
  produced (sha256 prefix `d23f4ff9137083ce`).
- `PROCESSING_CUDA_FILL_PROBE_BIN=<bin> sh scripts/check/check-processing-cuda-fill-native.shs`
  -> `processing_cuda_fill_native_status=fail reason=probe-failed`, probe line
  `reason=cuda-init-failed`. That is a runtime fault, not the collector: strace
  shows libcuda is never opened, and the linked binary has no `libcuda` string,
  so the linked `rt_cuda_init` does not dlopen the driver. Handed to the CUDA
  runtime/extern lane. It is not part of this record.

The aggregate `bug_db.sdn` row was still `open` even though the 2026-11-12 note
says it was synced to closed. It is now synced to `closed`.
