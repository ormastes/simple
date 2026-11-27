# Bug: seed native-build parent retains ~28 MiB per compiled file; Windows stage2 OOMs on 32 GiB hosts

Date: 2026-10-22
Lane: work/phase1-mcp-redeploy-20261021 (fresh worktree on origin/release_phase3, base 3b02fed6a0c)
Host: DESKTOP-5A4V03J, Windows 10 / Git Bash, x86_64-pc-windows-gnu, 12 CPUs, 33,195,332 KiB RAM
Producer: phase-1 seed (Rust, nightly-2026-09-15, cranelift), `native-build --mode dynload --entry src/app/cli/bootstrap_main.spl`

## Symptom

`--full-bootstrap --stop-after-stage2` cannot complete on this host. Five
distinct failure modes were observed across nine attempts, all tracing back to
one defect: the seed's native-build driver process retains compiled-artifact
memory in the parent roughly proportional to the number of files completed
(~28 MiB/file), with no spill/streaming, until allocation fails.

## Measured evidence (all 2026-10-22, same lane)

1. **RSS policy kills at any cap** (attempts 2, 3, 4, 6, 8; exit 88,
   `stage2-rss-cap-exceeded`). Peak is always cap + small overshoot, never
   below:
   - cap 5,859,375 KiB -> peak 5,859,620 / 5,859,972 KiB
   - cap 8,388,608 KiB -> peak 8,389,804 / 8,390,192 KiB
   - (default floor cap 5,859,375 KiB is `workers x ~1,146 MiB`; the seed's
     real per-worker footprint exceeds the policy's per-worker budget, and the
     parent retention dominates anyway, so no policy-derived cap admits the
     workload)
2. **Monitor mode reveals true growth** (attempt 7, `SIMPLE_BOOTSTRAP_RSS_CAP_MODE=monitor`):
   parent RSS observed at 2.3 GiB (early), 13.1 GiB at [550/711], 17.2 GiB at
   [600/711], ~20 GiB near the end - monotone growth against completed-file
   count, including periods of zero compile progress (pure aggregation).
3. **Allocation failure** (attempt 9, monitor + `SIMPLE_NATIVE_FILE_TIMEOUT=1200`
   + `--jobs 4`): stage2 log ends at `[600/711] compiled` followed by
   `memory allocation of 540688 bytes failed` (Rust std alloc error, seed
   process) once the process reached ~20 GiB RSS and host free RAM dropped
   under ~5 GiB. Free physical memory returned to ~25 GiB immediately after
   the process died, confirming the retention was the seed parent.
4. **Per-file worker timeouts under host contention** (attempt 7): with the
   default 300 s per-file cap and a second large native-build running, one
   worker timed out and the replacement admission refused all remaining files
   (`NOT_ATTEMPTED: previous native worker timed out; refusing replacement
   admission`) - 763 files lost to one timeout. Raising
   `SIMPLE_NATIVE_FILE_TIMEOUT=1200` removed this class (attempt 8/9).
5. `--low-memory` (single worker) is implemented in the seed
   (`native_build.rs --low-memory`, `NativeBuildConfig::low_memory` /
   `init_rayon_pool`) but only throttles parallelism; it does not change the
   parent retention curve, so it cannot fix this defect (it would still
   balloon to ~20+ GiB, just more slowly).

## Why other lanes see different symptoms

The parallel stage2 debugging lane (PRs #4124/#4126 and companions, 2026-10-22)
reports "stage-2 compiled 1485/0" reaching later phases - consistent with a
host whose RAM admits the full retention (~1485 files x ~28 MiB ~= 40 GiB).
On this 32 GiB host the same workload dies mid-compile, so later-phase
diagnostics (zero-sources, read-path) never reproduce here.

## Impact

- Windows hosts with <= 32 GiB RAM cannot produce a stage-2 compiler from the
  seed on release_phase3-era sources; `--stop-after-stage2` and every
  downstream phase (3/4, full CLI, MCP/LSP rebuild from phase 2) are blocked.
- The RSS policy's `enforce` mode makes the failure look like a resource-policy
  problem (exit 88) and hides the underlying allocation failure; `monitor` mode
  is required to see the real curve.

## Suggested directions (not attempted in this lane)

- Seed driver: stream compiled artifacts to the producer-scoped cache as
  completed and keep only handles/metadata in the parent (the objects already
  land in `--cache-dir`; the in-parent retention appears redundant).
- Alternatively bound parent retention with an LRU spill when a high-water
  mark is reached.
- Until fixed, stage2 on <= 32 GiB Windows hosts needs a producer whose driver
  does not retain (a fixed seed rebuild), or a host with >= 48 GiB RAM.

## Repro

```sh
# fresh worktree on origin/release_phase3, toolchain per
# doc/07_guide/tooling/local_temp_phase1_mcp_deploy.md (2026-10-22 update)
sh scripts/bootstrap/bootstrap-windows.sh --mingw --full-bootstrap \
  --stop-after-stage2 --mode=dynload --backend=cranelift --no-mcp --verbose \
  --output=<repo>/build/bootstrap/<lane>
# enforce mode: exit 88 at ~5.9 GiB (default cap)
# monitor mode: OOM at [600/711], ~20 GiB parent RSS
SIMPLE_BOOTSTRAP_RSS_CAP_MODE=monitor SIMPLE_NATIVE_FILE_TIMEOUT=1200 # same, later
```

## Related

- `doc/07_guide/tooling/local_temp_phase1_mcp_deploy.md` (2026-10-22 update) -
  the five host/toolchain prerequisites measured in the same lane.
- `doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md` -
  linked by the bootstrap's own stage2 failure warning.
- Parallel lane docs: PR #4124 (`zero-sources` Windows repro), PR #4126
  (actual candidate read path is `rt_file_read_text`).

## 2026-11-13 addendum: stage2-CANDIDATE (pure Simple) SCV surface phase retains far more, far earlier than the seed parent

Lane: work/release-1.0.0-mcp-local, MSVC (`--msvc --full-bootstrap
--stop-after-stage2 --mode=dynload --jobs=2`), tips 79201709202 (cycles 9-11)
and 9f00edbbaaf (cycle 12). Host: DESKTOP-VMF96U6, Windows 11, 64 GiB RAM,
Hyper-V dynamic-memory guest (see also
windows_balloon_memory_headroom_false_refusal_2026-11-13.md for the
AvailPhys side story on the same host).

The seed parent retention above is NOT the binding constraint on this host.
The stage-2 compiler-TESTS campaign (phase verification, profile=slim) fails
earlier and larger:

1. The main seed->stage2 native build COMPLETES under a 48 GiB tree cap
   (1657 modules, ~28 MiB/module seed retention fits).
2. The stage2-compiler-tests campaign then dies on the FIRST tool row
   (compiler_cli_build), still inside its phase-2 SCV surface scan:
   - cycle 9 (cap 36 GiB): peak 36.04 GiB, ~40 min, samples=24030
   - cycle 10 (cap 45 GiB): peak 45.17 GiB, ~20 min, samples=11953
   - cycle 11 (cap 48 GiB hard ceiling): peak 50.34 GiB, ~58 min,
     samples=34992, killed mid-surface-scan at seq=271 of the per-file
     `phase2:surface:file:parse-start/parse-done/surface-done/promote-done/
     commit-done/released` cycle (row log:
     stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/
     compiler_cli_build.log — the whole 361 KB log is ONLY this phase).
3. Rate: 271 files / ~58 min ~= 13 s/file for the surface scan alone in the
   pure-Simple candidate. At that rate the surface phase of a ~1300-file
   closure cannot finish inside any campaign timeout even with unlimited RSS
   (the rows already run SIMPLE_PARSE_SHARD_MAX=1: the pinned frontend does
   all parse/HIR in the row parent, so the retention accumulates in ONE
   process and nothing is spilled).
4. The 48 GiB static ceiling (tree-rss-policy.shs
   BOOTSTRAP_TREE_RSS_STATIC_CEILING_KIB, "sixth widening 2026-10-16: 48 GiB
   measures the true plateau") now UNDER-measures the plateau: the merged
   tree's surface phase alone exceeds 50 GiB. The elevated-ceiling ratchet
   (SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB) is unreachable on this host:
   it demands requested > previous (50331648) AND requested <= 3/4 host RAM
   (50148945) — an empty range.

Owner asks for the compiler lanes working the interface-closure / SCV
surface and HIR-decode areas:

- Stream or bound the phase-2 surface model per promoted file (the per-file
  "released" marker exists but RSS grows ~190 MiB per processed file across
  the phase — either the release is ineffective or the aggregate surface
  model legitimately holds everything).
- Explain/mitigate the 13 s/file surface-scan cost on the self-hosted
  candidate (warm SCV snapshot, warm HIR caches did not help; cycles 9-11
  shared one compiler sha so row caches were warm).
- Until then the MSVC stage2 slim verification matrix cannot pass on 64 GiB
  hosts, which blocks stage3/stage4 resume and the downstream MCP lane on
  this machine class.

Mitigations already applied and VERIFIED working on this lane (not the
blocker): SIMPLE_BUILD_MEMORY_RESERVE_BYTES + host mem_reserve_free_mib
(balloon false-refusal, #8931), SIMPLE_BUILD_MEMORY_RESERVE_BYTES /
SIMPLE_HOST_CONFIG excluded from module cache identity (#8948, cycle 10
reused 1655/1657 objects), explicit tree cap via
SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB (accepted up to the ceiling),
SIMPLE_NATIVE_FILE_TIMEOUT=1200 (worker-timeout class).
