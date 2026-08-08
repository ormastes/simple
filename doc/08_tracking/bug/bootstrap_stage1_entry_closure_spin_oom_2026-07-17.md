# Bootstrap Stage 1: seed native-build CPU-spins with runaway allocation on src/app entry closure (2026-07-17)

**Severity: release blocker.** Blocks the entire Linux redeploy chain: stage1
never completes → self-hosted binary cannot be rebuilt → deployed stale seed
(Jul 11) lacks `rt_cli_arg_count` → dozens of gate specs fail at semantic phase
(async_library_hardening 0/19, scheduler handoffs, riscv sidecar contract, ...).

## Repro

```
build/bootstrap/full/x86_64-unknown-linux-gnu/simple native-build \
  --source src/app --entry-closure --strip --threads 1 --timeout 180 \
  --entry src/app/cli/bootstrap_main.spl -o /tmp/out --backend=llvm-lib
```

(= what `bin/simple build bootstrap` runs as Stage 1.) Seed binary dated
Jul 16, 32 MB.

## Evidence (clean-worktree isolation, 2026-07-17)

- Reproduces on **unmodified HEAD** in an isolated git worktree — the dirty
  main-WC files are NOT implicated.
- Zero bytes of stdout/stderr for the whole run; killed by its own
  `--timeout 180` ("Compile failed (exit None)").
- Process state `R`, `wchan=0`, ~100% single-core CPU every sample — a live
  compute loop, not a deadlock.
- RSS ~linear, unbounded: 1.4 GB → 11.3 GB across t≈0→136 s (~70–110 MB/s),
  no plateau, no visible GC.
- gdb attach blocked by yama ptrace_scope; no stack obtained.
- Side observation: trivial entry with a bare (non-package) `--source` dir
  segfaults immediately (exit 139) — separate degenerate-layout defect.

## Update (same day): fresh seed does NOT spin

A seed rebuilt from current `src/compiler_rust` (`cargo build --profile
bootstrap -p simple-driver`) runs the identical command normally (24k
diagnostic lines in seconds, real parse errors instead of silence). The spin is
specific to the **Jul 16 prebuilt binary** at `build/bootstrap/full/` — either
a since-fixed seed bug or a corrupt/stale artifact. Remediation: rebuild the
full seed from source and replace the prebuilt; keep the isolation evidence
below for the record. Stage 1 then proceeds to the next blocker, the f-string
lexer regression (`seed_fstring_nested_quote_interp_2026-07-17.md`).

## Hypothesis (unconfirmed at source level)

`--entry-closure` module-graph walk lacks memoization or cycle detection —
re-visiting/re-allocating over the large, likely cyclic `src/app` import graph.
Next probe: rerun the same command with a freshly cargo-built seed
(`src/compiler_rust/target/bootstrap/simple`) to split seed-binary regression
vs. source-graph trigger; then bisect the import graph (e.g. shrink `--source`)
or instrument the closure walk.

## Related

- `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17.md` (stale
  deploy wall this blocks the exit from).
- Memory note `project_native_build_cannot_emit_2026-07-08.md` — earlier "seed
  cannot emit" wall was bisect-don't-patch; same discipline applies.

## Status (2026-07-18)

SUPERSEDED/PARTIALLY RESOLVED. Fresh cargo seed (built 2026-07-17 from src/compiler_rust) runs stage1-3 cleanly (rc=0, no spin). Jul-16 prebuilt artifact remains defective; replace with fresh cargo build.
