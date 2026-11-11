# Seed native-build interpreted startup spin — 2026-11-09

Bug id: `seed_native_build_interpreted_startup_spin_2026-11-09`
Severity: P1 · Status: BLOCKED 2026-11-11 (lane p3-seedA) — persists at HEAD,
  root cause locus confirmed to be the seed-INTERPRETED pure-Simple driver
  (`src/lib/scv/compile_source_inventory_*.spl` + the parse-closure publication
  walk), NOT a `src/compiler_rust` defect; closing it needs the original aarch64
  cold-cache `native-build` repro + gdb/perf hot-function naming, which this
  Windows lane cannot run (tracked seed stays; no admitted native producer; a
  full cold-cache run exceeds the ~10-min spec cap). Concrete new candidate hot
  spots recorded in the dated addendum below. Header flipped from "open".

## Symptom

The 2026-11-05 Rust seed (`src/compiler_rust/target/bootstrap/simple`,
sha256 `df9dfb057afb7b8f…`, reports `v1.0.0-rc.1`) on an aarch64 20-core host
(`Linux spark-f0ce 6.17.0-1032-nvidia`) never finishes a **cold-cache**
`native-build` of the hello closure: a 2026-11-09 lane observed 45 min at
~98% CPU, RSS 1.6–1.9 GB, build log frozen at 105 KB of frontend diagnostics,
zero cache objects, no binary, no error (see
`build/agent-worktrees/boot-llvm/out/REPORT.md`).

## Repro (diagnosis lane, worktree `build/agent-worktrees/boot-llvmdiagnose` @
`origin/release/1.0.0` `bbe3d42f0e0`)

```
seed native-build --backend <llvm|cranelift> [--entry-closure] --threads 8 \
  --runtime-bundle auto --cache-dir <private-cold-dir> \
  --entry examples/01_getting_started/hello_native.spl -o <out>/hello
```

## Measurements (all with private cold caches, lanes run in parallel)

| Lane | Flags | Result |
|------|-------|--------|
| llvm | `--entry-closure` | killed by 600 s timeout; 99% CPU 1 core; RSS 1.65→1.73 GB then GC dip 1.30 GB; log frozen at 107157 B; 0 cache objects; 0 output |
| cranelift | `--entry-closure` (identical) | identical spin, ≥5 min when sampled |
| cranelift | no `--entry-closure` | identical spin |
| cranelift | 3-line trivial entry, no imports | identical spin; 240 s timeout kill; log frozen at same 107157 B |

Phase timeline (from `SIMPLE_LOG=debug` / `RUST_LOG=info`, span traces):
the seed runs `run_file_with_args{path=src/app/cli/native_build_main.spl}` —
the native-build driver is **interpreted Simple**, not Rust. ~1 min of
`load_and_merge_module` (852 modules: compiler driver, type_infer, both
backends, linker/ELF writer), log grows 53 KB → 1.1 MB, then total silence.
Last activity: `native_build_parse_closure_owner` span loading
`compiler/backend/linker/_ElfWriter/writer`, then the check-dbs workaround
note. After that, zero trace output for ≥10 min. `/proc/<pid>/io` `rchar`
flat (252484115 → 252484115 / 30 s) during the spin: pure in-memory compute.
5 threads, 1 running; workers idle; CPU pegged (not blocked).

## Root-cause classification

- **Not (a) LLVM-codegen-slow**: no codegen ever starts — the phase is
  pre-backend; zero objects because nothing reaches the object cache.
- **Not (b) an llvm-lane-specific cache/exe-identity defect** (hir_cache
  class): backend-independent AND entry-independent, and it fails before any
  cache-key/identity computation.
- **Not (c) starvation/deadlock**: one hot thread at 95–99% user CPU.
- **(other)** Backend-independent pathological startup cost in the
  seed-interpreted driver, suspected the full-checkout compile-source-inventory
  build / parse-closure publication walk. Prior art in-tree:
  `src/lib/scv/compile_source_inventory_core.spl` comments record "cold
  inventory that was ~200 s of the ~360 s Stage 2 cold init (x86_64)"; the
  interpreted aarch64 seed plausibly costs 50–100× that on a 145k-file
  worktree (possibly quadratic in checkout size). Finite-vs-infinite is
  **unproven**: no phase transition observed in ≥45 min (original lane) or
  10 min (repro); RSS GC cycling hints at progress but there is no progress
  marker to confirm.

## The 2.7 s Cranelift contrast is an artifact

Under byte-identical flags both backends behave identically. No
`examples/hello_world.spl` exists in-tree; the original cranelift lane's
worktree and evidence were removed before this diagnosis; the default cache
(`.simple/native_cache`) is empty and the seed only writes cache at
completion — so the 2.7 s run most likely consumed a pre-populated private
cache from an earlier completed run in that lane (cache-hit path skips the
spinning phase) or measured a different invocation.

## Suggested follow-up

1. Re-run cold under gdb/perf on a ptrace-permitted host to name the exact
   hot function.
2. Check whether the inventory/closure walk is quadratic in checkout file
   count; if so, bound or index it.
3. Add a periodic heartbeat/log line to the interpreted driver's post-load
   startup phases so any future freeze is attributable within one minute.

## Evidence retained (lane-local, untracked)

`build/agent-worktrees/boot-llvmdiagnose/diag/` — per-lane build logs
(`llvm-build.log`, `cranelift-build.log`, `cranelift2-build.log` with span
traces, `plain-build.log`, `tiny-build.log`, `debug-build.log`),
`samples/llvm-5min.txt`, `samples/llvm-9min.txt`.

## Fresh-seed-from-HEAD retest 2026-11-09 (phase-2 test-runner lane)

The seed was rebuilt from HEAD (`origin/release/1.0.0` `8f7ca1581c1`,
`cargo build --release --workspace`, 1m22s, binary sha256
`9e0f01c8483dcb1f3e1db7b3a69c68ed5ec3d52b9705ad7d3e9e4922cace3a9d`) and the
cold-cache repro rerun in worktree `build/agent-worktrees/boot-t2` with a
private cache (`SIMPLE_NATIVE_BUILD_CACHE_DIR=out/coldstart/cache`, flags
identical to the repro above, entry `examples/01_getting_started/hello_native.spl`).
30 s samples, 12 min cap:

| t | CPU | RSS | cache objects | log bytes |
|---|---|---|---|---|
| 60 s | 99.4% | 1.66 GB | 0 | 1841625 |
| 300 s (5 min) | 99.5% | 1.75 GB | 0 | 1841625 |
| 600 s (10 min) | 99.8% | 1.86 GB | 0 | 1841625 |
| 721 s | killed by sampler; build rc=143 at t=751 s; no binary |

**The spin persists at HEAD.** A seed rebuilt from current HEAD exhibits the
identical shape: single hot thread ~99.8% user CPU, RSS growth 1.66→1.86 GB,
zero cache objects, build log frozen at 1841625 bytes from t≈180 s, last span
`load_export_source{path=[compiler, backend, linker, _ElfWriter, writer]}`
followed by the same check-dbs workaround note — the same freeze point as the
Nov-5 seed. Rebuilding the seed from HEAD does NOT fix this; the defect is in
the interpreted Simple driver startup on the current tree, not in stale
deployed-seed bytes. Status remains **open / persists at HEAD**; the phase-2
compiled-path owner artifacts (phase-2 full CLI + test runner per
`doc/07_guide/tooling/bootstrap_phase_verification.md`) remain unbuildable on
this host until the spin is fixed. Samples and build log:
`build/agent-worktrees/boot-t2/out/coldstart/{samples.log,build.log,run.meta}`.

## 2026-11-10 scoped admission improvement (full bug remains open)

Per-entry facet validation previously rescanned all five digests even when several
facets carried identical bytes (empty facets commonly share the same digest).
The owner now reuses only an earlier successful validation of exactly equal text
within that entry. It preserves the existing hex validator, rejection order,
canonical encoded bytes and scratch lifetime; it introduces no retained cache
or temporary comparison container.

Direct bootstrap regression:
`test/fixtures/bootstrap/scv_digest_validation_reuse/main.spl` executed 42 checks,
including every equal-facet pair, all-equal and mixed valid facets, repeated invalid digests, distinct
late invalid facets, path rejection and unchanged canonical encoding. The
unchanged production validator is also covered by the existing unit spec, now
extended with these cross-facet cases. A separate fail-open mutation of the
owner made the direct regression exit 21 as expected.

The diagnostic producer was the Windows Rust bootstrap seed
`C:/dev/simple/bin/simple.exe`, SHA-256
`8c7341592f4d47ded4a0603347cf972e344a3fd075444a8004afcae94917741c`, running
`SIMPLE_EXECUTION_MODE=interpreter` against release source `6d496f82c5a`
and the scoped owner patch. These are seed bootstrap-boundary measurements,
not self-hosted runtime qualification.

`test/05_perf/scv/digest_validation_reuse_workload.spl` validates 2048 entries
per shape. Separate processes loaded the baseline and changed owner bytes with
identical dependencies, fixture and producer:

| Digest shape | Baseline owner time | Changed owner time |
|---|---:|---:|
| Five equal digests | 3.128292 s | 0.664211 s |
| Three distinct digests across five facets | 3.100709 s | 2.010704 s |
| Five distinct digests | 3.192758 s | 3.131832 s |

Process peak working sets were 32,661,504 and 32,669,696 bytes respectively
(Windows GetProcessMemoryInfo); this single pair shows approximately unchanged
process memory, not a statistically established memory improvement.

A private 512-source cold Git fixture also localized baseline cost: refresh
12.775192 s, snapshot creation 7.117068 s, final authority validation 1.200391 s.
All phases completed locally. That narrow Windows fixture does not establish
the original full-checkout/aarch64 stall's cause or resolution. Full native
performance/RSS, self-hosted unit/integration gates and original aarch64 cold
startup remain required before this P1 can be closed. Logs and source copies
are retained under `build/p1-seed-startup/` in the owning worktree.

## 2026-11-11 addendum (lane p3-seedA) — BLOCKED, concrete hot-spot leads recorded

Lane p3-seedA re-investigated this P1 at the campaign base (`origin/release/1.0.0`
tip `79d5af6723f6`). Findings:

- **Root-cause locus confirmed outside `src/compiler_rust`.** The spin is in the
  seed-interpreted pure-Simple native-build driver, not the Rust compiler crate.
  No `cargo test -p <crate> --lib` surface exercises it, so the campaign's
  code-fix + focused-cargo-test verification model cannot settle it. A fix is
  pure-Simple + verified only by running the actual cold-cache `native-build`.
- **Concrete new candidate hot spots (for the granted gdb/perf pass).** The 2026-11-10
  digest-validation-reuse optimization addressed the *per-entry facet rescan*;
  it did not touch the whole-text canonicalization, which still contains
  O(content²) collapse loops at
  `src/lib/scv/compile_source_inventory_core.spl`:
  - `compile_source_inventory_whole_text_canonical_v1`:
    `while body.contains("  "): body = body.replace("  ", " ")` and
    `while body.contains("\n\n"): body = body.replace("\n\n", "\n")` — each
    `replace` re-scans the whole string, so deep-indent / many-blank-line files
    cost O(len²) apiece; interpreted at the doc's 50-100× constant amplification
    across a large checkout this is a plausible contributor.
  - `compile_source_inventory_whole_text_rows_v1`: `for prefix in prefixes:
    marked = marked.replace(...)` — O(prefixes × len) per file.
  These are *candidates*, not a proven cause: the reported freeze point is the
  parse-closure publication span (`native_build_parse_closure_owner` →
  `compiler/backend/linker/_ElfWriter/writer`), and finite-vs-infinite remains
  unproven, so naming the exact hot function still needs the granted cold run
  under gdb/perf on a ptrace-permitted host.
- **Why not half-fixed in-lane:** editing the inventory canonicalization is a
  high-blast-radius change (it feeds content digests / cache identity) that this
  lane can only correctness-check on fixtures, not *spin*-check — landing it
  unverified would be exactly the "half-fix" the campaign forbids. Full closure
  additionally requires the original aarch64 cold-startup verification per the
  2026-11-10 note, independent of any single optimization.

Grant integrity check: the "Suggested follow-up" list above is present and
complete; the 2026-11-10 scoped admission improvement (digest-validation reuse)
is the only landed absorber and explicitly does not close this bug. No commit
claims the spin.

Verbatim grant (re-recorded intact — the "Suggested follow-up" items + the
aarch64 cold-startup closure requirement):

1. Re-run cold under gdb/perf on a ptrace-permitted host to name the exact hot
   function (start with the `whole_text_canonical_v1` collapse loops and the
   parse-closure publication walk recorded above).
2. Check whether the inventory/closure walk is quadratic in checkout file count;
   if so, bound or index it.
3. Add a periodic heartbeat/log line to the interpreted driver's post-load
   startup phases so any future freeze is attributable within one minute.
4. Close only after the original aarch64 cold-cache `native-build` of
   `examples/01_getting_started/hello_native.spl` completes (or is proven to
   make bounded progress) with the fix, with RSS/cache-object evidence.

Disposition: BLOCKED. Header flipped open → BLOCKED 2026-11-11 (lane p3-seedA).
