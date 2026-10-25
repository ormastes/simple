# Per-file worker pool: children get argv[0] twice; pool skip is silent

Found on the phase-3 stage3 run (new stage2 @ f9d07913dcc, Windows, SIMPLE_FILE_WORKERS=1).

1. **Child argv0 duplication (fixed in work/file-worker-child-argv).** `run_native_file_worker_v1`
   receives bootstrap_main's full `get_cli_args()` (argv[0] = own exe). `native_file_worker_child_args_v1`
   copied argv[0] into the HIR/MIR child argv and `process_spawn_async(simple_bin, ...)` prepends the exe
   again, so every child printed `error: unknown command '<exe>'` (16/16 HIR children exit=1, claimed=0)
   and the coordinator failed closed: "per-file route selected but the file-worker pool produced no sealed
   ledger". Fix: child argv starts at the `native-build` token.

2. **Silent two-pass fallback (open).** `run_file_worker_pool_v1` (native_build_main.spl) admits
   `parallel = min(hir_count, mir_parallel)`; with the default SIMPLE_MIR_SHARD_WORKER_KB=16000000 the
   first attempt got `hir_count=5 mir_parallel=0` and printed one `[file-worker] not admitted ...; two-pass
   path` line, then ran the old global-HIR path for ~5 min before anyone noticed. Needed: a loud warning
   (and receipt field) when the per-file route was selected but not admitted, and per-worker budgets sized
   from the measured per-module peak (#4770) instead of a 16 GB constant. Workaround used:
   SIMPLE_MIR_SHARD_WORKER_KB=2500000 SIMPLE_HIR_SHARD_WORKER_KB=2500000
   SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=70000000 -> `[file-worker] workers=16`.
