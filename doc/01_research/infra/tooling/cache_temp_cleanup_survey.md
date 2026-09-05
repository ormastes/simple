# Cache / Temp Cleanup Survey (2026-08-02)

Research for `simple clean` (manual) + auto cleanup on `simple build` start.
Measured on the primary dev checkout at `/home/ormastes/dev/pub/simple`.

## 1. Repo-side inventory

| Candidate | Measured size | Class | Notes |
|---|---|---|---|
| `build/` (total) | **155 G** | SAFE (mostly) | All regenerable; rebuild cost varies per subtree (below) |
| `build/bootstrap/` | 70 G | SAFE / HIGH rebuild cost | Stage artifacts; full re-bootstrap ~hours |
| `build/coverage-bootstrap-586*` | 16 G+ | SAFE | Coverage dumps from finished campaigns |
| `build/os/` | 13 G | SAFE / HIGH rebuild cost | SimpleOS toolchain + disk images |
| `build/bootstrap-beta2-local*`, `build/u128_work`, `build/evidence-*`, `build/bootstrap-segv-fix`, `build/isolated_*`, `build/wm_harden`, `build/fable_s2` | 4–9 G each | SAFE | One-off campaign work dirs; classic stale-LRU candidates |
| `build/tmp/` | 361 M | SAFE | Toolchain scratch |
| `build/test-artifacts/`, `build/test*` | ~13 M | SAFE | Test logs/artifacts |
| `build/gpu_runnable_report.txt` | small | SAFE | Regenerated report |
| `build/freebsd/` (`vm/*.qcow2.xz` base image) | 69 M | SAFE but re-downloadable | Base image re-fetched by wrapper; overlays recreated per run. Separate target (`--qemu-images`) so a normal `--build` clean does not force a re-download |
| `src/compiler_rust/target/` | **131 G** (debug 115 G, release 8.9 G) | SAFE / MEDIUM rebuild cost | Cargo caches; by far the densest single win. Debug tree dominates |
| `target/` (repo root) | 8 K | SAFE | Vestigial |
| `/tmp/simple_*`, `/tmp/spl_*` | varies | SAFE with grace period | Test runner / MCP / check scripts leave `simple_*` fixtures, sqlite files, jsonl inputs (e.g. `/tmp/simple_app_mcp_intensive_input.jsonl`, `/tmp/simple_check_diagnostics_*.spl`). ~12+ app files write under `"/tmp` (`src/app/cli/bootstrap_check.spl`, `src/app/test/*`, `src/app/compile/*`, …). Must never delete files younger than a grace window — parallel agent sessions are live |
| `.spipe/` | 8.5 M | **NEVER-TOUCH** | Active agent lane state; tiny anyway |
| `doc/08_tracking/`, `doc/10_metrics/` | n/a | **NEVER-TOUCH** | Auto-generated but **tracked in git**; deleting creates dirty tree / clobber risk |
| `bin/release/<triple>/` | 1.4 G | **NEVER-TOUCH (auto)** | Deployed self-hosted tooling — deleting it bricks `bin/simple`. Manual-only, and only with an explicit future flag (not implemented) |
| `.git/` objects | large | **NEVER-TOUCH** | Heavy jj snapshot churn creates loose objects. `git gc --auto` exists but jj-colocated repos are sensitive (op store references, concurrent agent sessions force-pushing). Document only — `simple clean` must never invoke git gc |

Total realistic reclaim on this machine: ~286 G, of which ~115 G (cargo debug)
is low-rebuild-cost and ~70 G (bootstrap) is high-rebuild-cost.

## 2. Other-tool practice survey (from knowledge, no network)

- **cargo**: no auto-clean at all; `target/` grows unboundedly. Community fix is
  `cargo-sweep` (delete artifacts older than N days / not built by current
  toolchain). Lesson: age-only sweeping misses the "huge but recent" case.
- **npm**: content-addressed cache (`_cacache`), self-healing on corruption,
  `npm cache verify` garbage-collects invalid entries. No size cap by default;
  explicit `npm cache clean --force` required. Lesson: verification ≠ size
  control.
- **pip**: `~/.cache/pip` unbounded; only manual `pip cache purge/remove`.
- **ccache**: the gold standard — LRU with a size cap (default 5G), cleanup
  triggered *on write* when the cap is exceeded, cleans down to a fraction of
  the cap (not exactly to it) so cleanup is amortized, stats kept per subdir so
  the threshold probe is O(1).
- **bazel**: `--disk_cache` had **no GC at all** for years (notorious disk
  filler); recent versions added `--experimental_disk_cache_gc_max_size` /
  age-based GC run at server idle. Lesson: shipping a cache without GC is a
  known failure mode.
- **git**: `gc --auto` uses a cheap object-count threshold probe
  (`gc.auto=6700 loose objects`) at command end; full gc runs only when
  exceeded; `gc.pruneExpire=2 weeks` grace period protects concurrent writers.
- **uv / pnpm**: content-addressed store shared across projects; `uv cache
  prune` / `pnpm store prune` delete only entries no longer referenced —
  reachability-based, still manual.

### Extracted design rules
1. **Size-capped LRU beats age-only** (ccache vs cargo-sweep): a cap bounds the
   disk footprint; age alone does not.
2. **Auto-clean must be cheap to CHECK**: a threshold probe at command start
   (git's object count, ccache's per-dir stats); the full clean runs only when
   the probe exceeds the cap.
3. **Clean down to a fraction of the cap** (ccache: ~80%) so cleanup is not
   retriggered on every subsequent run.
4. **Grace period / never delete in-use** (git pruneExpire): recent-mtime files
   are skipped; concurrent sessions must be assumed.
5. **Dry-run is first-class** (`--dry-run` everywhere; print sizes before act).
6. **Auto mode must be opt-out-able** (env var), and must **fail open** — a
   stat error must never block the build.

## 3. Consequences for `simple clean`

- Manual targets: `--build`, `--cargo`, `--qemu-images`, `--temp`, `--all`.
- Hardcoded NEVER-TOUCH list (positive allow-roots + deny prefixes), realpath
  containment before any delete.
- Auto mode: threshold probe on `simple build` start only (never `test`/`run`
  hot paths), `SIMPLE_CACHE_MAX_GB` cap (default 20 G), delete SAFE class
  oldest-first (mtime LRU) down to 80% of cap, one summary line, fail-open.
- git gc: documented above, never invoked.

Design/plan: `doc/03_plan/infra/tooling/simple_clean_plan.md`.
