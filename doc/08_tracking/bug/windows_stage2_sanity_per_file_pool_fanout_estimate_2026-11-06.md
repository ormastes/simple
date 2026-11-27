# Windows Stage 2 sanity: per-file worker pool can never admit two workers on a 32 GiB host

Status: probe fix + host reserve landed 2026-11-06; compiler pool default still OPEN (see "Follow-up").
Host: DESKTOP-5A4V03J (Windows, 32 GiB, MinGW clang lane, `--backend=cranelift`).

## Symptom

Every Stage 2 bootstrap on this host since 2026-10-27 rejects a working
candidate at sanity: the candidate compiles and links all 1576 modules, then the
`scv_prime` / `p2_add` frontend probe fails with

```
error: per-file worker pool refused (hir_workers=0 mir_workers=0, need >= 2):
not enough free memory for 2 workers ... Free memory=18247964 kB,
per-worker budget=9000000 kB (HIR 9000000 kB, MIR 9000000 kB),
need >= 30000000 kB free.
```

(earlier runs on a busy host: `build refused: ... below the 16208 MiB reserve`).
Waiting for an idle host cannot help: an idle 32 GiB host has ~18 GiB free.

## Cause

- `88f86fd749b` (2026-10-27) made a refused per-file worker pool fail closed
  (before, it fell back to an in-process build, which is how the 2026-10-25
  Windows sanity passed).
- The probes inherit the fanout-host per-worker estimate (9000000 KiB) although
  the canonical Windows frontend owner pins one frontend at 3000000 KiB
  (`scripts/bootstrap/lib/product-frontend-policy.shs`).
- The pool headroom default is a flat 24 GiB (`SHARD_TREE_HEADROOM_KB_V1`,
  `src/app/cli/shard_mem_clamp.spl:428`), while the start guard already scales
  to min(24 GiB, RAM/2) (`build_memory_reserve_default_kib_v1`, `:688`).

Measured: the `p2_add` probe build peaks at 3289 MiB working set for the whole
process tree (retained candidate, 2026-11-06).

## Fix (this change)

- `candidate_frontend_admission.shs`: on Windows the probes default
  `SIMPLE_{HIR,MIR}_SHARD_WORKER_KB` to the Windows policy share (3000000);
  explicit caller values still win.
- `config/host/DESKTOP-5A4V03J.sdn`: `mem_reserve_free_mib: 10240` (read by
  both `host-env.shs` and `std.nogc_sync_mut.host_limits`).

## Follow-up (open)

Make the pool headroom default host-scaled like the start guard
(`shard_tree_headroom_kib_for_v1` should fall back to
`build_memory_reserve_default_kib_v1(total)`), so other 32 GiB hosts need no
per-host override. Compiler change; needs a Stage 2 rebuild to take effect in
the sanity probes.

## Second fix 2026-11-06: single-process probes on Windows

With the 3000000 KiB estimate the MIR pool admitted 3 workers but the HIR pool
still admitted 0: it sizes from a declared tree budget (none on Windows) and,
when one is declared, spends only part of it after reserving the coordinator
peak (~1.3 GiB), clamped again to free - reserve. Declaring 6000000 KiB still
gave `hir_workers=0`. Windows policy pins ONE frontend, so the probes now set
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` (the explicit single-process build the
refusal itself names; the shape that passed before 88f86fd749b).

The probe's compiler also does not see `config/host/<hostname>.sdn` (it runs
from an isolated temp root), so the start guard fell back to min(24 GiB,
RAM/2) = 16208 MiB. The host's `mem_reserve_free_mib` is therefore forwarded
through the sanctioned `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` at bootstrap
invocation (`$(host-env.shs --get mem_reserve_free_mib) * 1 MiB`).

Result, release `060ecf462c5` + this change: Stage 2 sanity `status=pass`
(p2_add, scv_prime, hello_world_positional all rc 0); admitted
`stage2-admitted/simple.exe` sha256 4a2a5d2d67425b962731ba97bda607de2c03ce06b50ec34657e67e349908e981.

Open follow-ups (compiler): pool headroom default host-scaled like the start
guard; host config lookup reachable from the probe's isolated root; Windows
HIR pool should accept the single-frontend policy without whole-program.
