# Windows MIR shard lane: 3,000,000 KiB tree share admits no worker; 25 GiB MIR owners cannot fan out under a 28 GiB cap

Status: one accounting fix landed (codegen peer divisor); the Windows share
policy and the MIR owner footprint are recorded here as owner decisions, not
changed.

Evidence: the rb5 Windows P3->P3 lane
`C:/dev/simple-release-boot-20261122/build/rboot/manual-p3to3-rb5.prev-stack1m/manual-p3to3.log`
(release/1.0.0 `0285176e3a7b`, `--threads 4`, 1,628-module closure, 64 GiB host,
a sibling P3->P4 lane running at the same time). Lines quoted below are from
that log; nothing here was re-run.

## Defect 1: `declared 3000000 kB` comes from the frozen Stage 3 transcript, not from the cap

```
[shard] threads=0 (requested 4, ..., tree budget=3000000 kB (declared 3000000 kB, cgroup memory.max 0 kB), worker budget=3000000 kB, parent peak=2752752 kB)
[shard] threads=1 (requested 4, ..., tree budget=3000000 kB (declared 3000000 kB, ...), worker budget=26072420 kB, parent peak=-1 kB)
[mir-shard] shards=16 parallel=1 ledger=.../hir/mir-queue-11796-0
[NATIVE] codegen: 16 uncached module(s), concurrency=1 (serial lane in this process: one worker admitted (cpus=24 budget_kib=3000000 resident_kib=22840248 headroom_kib=2975200 ... peer_shards=4))
```

`declared` is `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` read at
`src/app/cli/shard_mem_clamp.spl` (`shard_threads_mem_cap`, :951). The lane
runs `env -i` over the replayed Stage 3 transcript
(`.../stage3/x86_64-pc-windows-msvc/stage3-command.transcript`), and that
transcript carries `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=3000000`,
`SIMPLE_HIR_SHARD_WORKER_KB=3000000`, `SIMPLE_PARSE_SHARD_MAX=1`. The value
was written by the Windows frontend owner when the transcript was frozen:

- `scripts/check/lib/bootstrap-stage3/command-snapshot.shs:425-427` sets the
  shard budget to the enforced RSS cap on every host, then the `MSYS*|MINGW*`
  case (:429-446) replaces it with
  `bootstrap_stage3_windows_frontend_environment "$cap" "$mode"
  "${SIMPLE_BOOTSTRAP_FRONTEND_MEMORY_BUDGET_KIB:-3000000}" "$ceiling"`, whose
  default 5th argument `budget_max=3000000` (:316) refuses any larger share.
  The comment at :432 states the intent: "Owners may allocate a smaller share,
  never enlarge this default into CPU-count fanout."
- `scripts/bootstrap/lib/product-frontend-policy.shs:43-55` mirrors the pin
  for product lanes (`product_policy_default=3000000`, `max=3000000`), already
  lifted for every non-Windows host ("A separate 3000000 KiB share pinned one
  HIR worker at any --threads") and for Windows per-file products
  (`SIMPLE_FILE_WORKERS=1`).

The lane's own knob, `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=29360128`, is
never read by the compiler. The compiler reads `SIMPLE_PROCESS_TREE_RSS_CAP_KIB`
(`shard_mem_clamp.spl:955`, `file_worker_pool_refusal.spl:179,:319`), and
`scripts/bootstrap/run-process-group-timeout.shs:64` maps only the other
direction. In a watchdog-run lane `process-tree-rss-watchdog.pl` exports the
enforced cap as the tree budget; this manual lane bypasses the watchdog, so
the stale transcript value is the only budget the compiler sees.

Why the one-worker share now admits zero HIR workers: the 2026-10-24 change
reserves the coordinator's measured peak out of the tree before pricing
workers (`shard_threads_parent_cap_for`, :689-702). With tree 3,000,000 and
`parent peak=2752752`, `reserve = max(2752752, 1200000)` leaves 247,248 kB,
i.e. 0 slots at 3,000,000 per worker. The share was meant to buy one HIR
worker; after that reserve it buys none, and the HIR phase falls through to
the in-process serial path. This affects the sanctioned Windows Stage 3 as
well, not only the manual replay.

Proposed repair (owner decision, not applied here because it reverses the
documented :432 position and is pinned by
`scripts/bootstrap/tests/windows-frontend-resource-policy-test.shs:49-62`,
`product-frontend-policy-test.shs` (non-fanout branch),
`phase-c-frontend-policy-test.shs`, `watchdog-shard-budget-export-test.shs`
and the `product-qualified-*` tests): in enforce mode let the Windows case use
`$bootstrap_stage3_run_rss_cap` as the share, as :425-427 already does for
every other host, and raise `budget_max` to the resolved ceiling; keep the
Windows worker estimates (3,000,000 HIR / 1,650,000 parse) unless re-measured.
The hazard the pin guarded against -- a Windows run without a tree budget
fanning out on a wrong host-memory reading -- is closed at the root by the
watchdog export (`shard_mem_clamp.spl:500-518`). Until then a manual lane that
wants the cap to drive admission must set
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=<cap>` and
`SIMPLE_PROCESS_TREE_RSS_CAP_KIB=<cap>` in its replayed env.

## Defect 1b (fixed): codegen pool divided the share by queued batches, not live owners

Each MIR owner's codegen pool reported `peer_shards=4` while exactly one owner
was live (`parallel=1`). `native_codegen_live_peer_shards_v1`
(`src/compiler/80.driver/driver_build/native_codegen_pool_v1.spl:215`) falls
back to `min(--mir-shard total, --threads)` when `SIMPLE_NATIVE_FILE_WORKERS`
is absent; the file-worker pool exports that variable with its live size
(`native_build_main.spl` phase B) but `run_mir_shards` did not. It now exports
`run_parallel` around `run_ledger_shards("mir-shard", ...)`. The variable is
scheduling-only and excluded from the native cache identity
(`cache/native_build_environment_identity.spl:167,:282`). On this host the
pool still admits one llc worker, honestly: `resident_kib=22840248` exceeds any
share and host `headroom_kib` was 1.7-4.1 GiB; the divisor is simply correct
now. Pinned by the new `it` in
`test/01_unit/compiler/driver/native_codegen_pool_v1_spec.spl`.

## Defect 2: MIR owners cannot run in parallel under 28 GiB because each holds the whole-closure HIR

The 26,072,420 kB MIR price (`1628 x SHARD_MIR_WORKER_PER_MODULE_KB_V1`) is
not an over-estimate on Windows. The owners' own `GetProcessMemoryInfo`
working set (the same API that gave the coordinator's 2.75 GiB peak) reaches
`[mir] ... rss_mib=24837`, and the codegen admission line in every owner shows
`resident_kib=22840248..24881932`. Two owners need ~50 GiB; a 28 GiB cap, or
60% of the 30.6 GiB then free, admits one. Lifting the declared budget alone
does not change `parallel=1` for this closure. The real cost is architectural:
a `--mir-shard` owner lowers or adopts HIR for all 1,628 modules and keeps it
resident while lowering its 1/16 of the MIR.

Workers do consume the coordinator's HIR cache, so this is not a re-parse of
the closure by design: the coordinator logs `[hir-cache] adopted=0
lowered=1628`, and all 17 owner processes log `[hir-cache] adopted=1567
lowered=61` and `[hir-cache] hits=1567 misses=61 stores=0 refused=61
reason=decode rejected=absent:61`. What every owner redoes:

- parse of all 1,628 files (`phase3:hir:file:start` is logged by both
  `driver_hir_pipeline_lowering.spl:1523` and `:2211` for every file in every
  process: 58,608 lines = 36 passes x 1,628), and
- HIR lowering of the 61 modules the coordinator could not store:
  `[hir-cache-store] refused reason=decode detail=reader kind=malformed
  detail=truncated line=335078/335078 module=.../src/app/cli/native_build_main.spl;
  entry not stored` (`driver_hir_cache.spl:1226`, 18 processes x 61). The
  store-side self-decode of the largest modules fails on a truncated last line,
  so the biggest HIR entries are exactly the ones every owner re-lowers.

Making an owner hold only its shard's HIR (or a cheaper adopted form) is not a
cheap change and is not attempted here. Two concrete follow-ups fall out of the
evidence: the `truncated line=335078/335078` encoder/decoder round-trip
refusal on 61 modules, and whether the adopted-HIR path can skip the parse
pass for cache-hit modules.

## Defect 3: the recorded MIR owner peak is contaminated by the sibling lane

`[mir-shard] measured worker peak commit=61888492 kB (static estimate 26072420
kB, previous run 0 kB)`. `shard_commit_live_footprint_v1` attributes the whole
host commit delta since pool start to the live workers; with one owner live
and a 28 GiB sibling lane growing beside it, 61.9 GiB was booked against one
owner. `run_ledger_shards` persists that as
`<ledger parent>/mir-shard.<producer>.peak_kib` and the next run of the same
producer starts its estimate there (`shard_worker_estimate_kib_v1`: measurement
can only raise). A following run on this host would price one MIR owner at
61.9 GiB. No code change here; the record names the mechanism.
