# Build / Lint Fast Path

Measured on this host **2026-08-09**. Every number below was observed with
`/usr/bin/time`; nothing here is estimated. Wall times are noisy because many
agents share this machine — treat them as magnitudes, not constants.

## 1. The headline: lint is ~100x slower than the number in circulation

The figure agents quote (`lint pays 4.4s / 339MB per run`) is **stale**.
Measured today, single file, `bin/simple lint`:

| target | bytes | wall | max RSS |
|---|---|---|---|
| `scratch/s0.spl` (24 B, 1 fn) | 24 | **11.70s** | 348 MB |
| synthetic, 25 fns | 1,355 | **94.51s** | 349 MB |
| synthetic, 50 fns | 2,730 | **209.97s** | 350 MB |
| `src/lib/common/base_encoding.spl` (120 lines) | 4,925 | **118.79s** | 366 MB |

RSS matches the historical 339 MB; **wall time does not**. Cost model:

```
lint wall ≈ 11.7s fixed startup  +  ~3.3–4.0s per function declaration
```

and the per-declaration term is **superlinear** (25→50 fns is 2.0x the input
but 2.4x the work, ≈ n^1.25). It is driven by declaration count, not byte
count: `base_encoding.spl` is 1.8x the bytes of the 50-fn synthetic but costs
half as much.

### Batching does NOT help — do not "just pass more files"

Linting two files in one invocation exceeded **600s** while one file took
119s. You pay the 11.7s startup once, but the superlinear per-declaration term
more than eats the saving. The startup tax is only ~10% of a real-file run, so
amortizing it is not where the win is.

### Where the time actually goes

Same file (`base_encoding.spl`), `fmt --check` parses but runs no lint rules:

| phase | wall | share |
|---|---|---|
| fixed startup (383 modules, no cache) | 11.7s | 10% |
| parse + format (`fmt --check` = 36.15s total) | 24.5s | 20% |
| **lint rules** (`lint` 118.79s − `fmt` 36.15s) | **82.6s** | **70%** |

**The lint rules dominate.** Caching module load, or batching to amortize
startup, addresses the smallest of the three terms.

## 2. Use the cached lint wrapper

`scripts/check/lint-cached.shs` skips files whose exact content was already
proven clean by the same binary, config, and options.

```bash
sh scripts/check/lint-cached.shs src/lib/common/base_encoding.spl
```

Measured, same file:

| run | wall | max RSS |
|---|---|---|
| cold (empty cache) | **152.00s** | 373 MB |
| warm (cache hit) | **0.03s** | 3.8 MB |

It cannot weaken a check, and this was verified rather than asserted:

- **Only clean results are cached.** A file with findings is never written to
  the cache. Verified: a file with findings reported `FAIL` on the first run
  *and* on the second.
- **Content change invalidates.** Verified: editing a previously-clean file
  produced `0 cached, 1 linted`.
- The key covers linter binary identity (`readlink -f` + size + mtime),
  `simple.sdn`, and the normalized option set.
- `--fix`, `--all`, `--mcp-perf` bypass the cache (their output is not a
  clean/dirty verdict).
- No hasher, unreadable file, or any other doubt falls through to a real run.

Escape hatches: `SIMPLE_LINT_CACHE=0` bypasses, `SIMPLE_LINT_CACHE_DIR`
relocates (default `build/lint-cache`).

### Caveat: binary churn defeats the cache in this shared working copy

The 0.03s figure is real but was measured back-to-back. **Sustained benefit
depends on `bin/simple` holding still, and today it did not.** Three distinct
release binaries were observed in a single session:

| observed | size |
|---|---|
| Aug 8 12:14 | 29,573,408 |
| Aug 9 04:30 | 58,940,120 |
| Aug 9 04:50 | 29,577,536 |

Every rebuild changes the key prefix and correctly invalidates every entry —
two consecutive wrapper runs both reported `0 cached, 1 linted` for this
reason, with identical content hashes but different binary prefixes. That is
the cache being *honest*, not broken: a new linter may produce new findings, so
replaying an old verdict would be exactly the "weakened check" this must never
do. The practical consequence is that **the cache pays off within a stable
window between rebuilds**, and in a busy shared WC that window can be minutes.
Check before relying on it:

```bash
stat -c '%s %y' "$(readlink -f bin/simple)"
```

Verdict line is always last on stdout: `PASS — n file(s) checked (h cached, m
linted)` / `FAIL — ...` / `ERROR — nothing was checked`.

## 3. Footguns — confirmed still live on 2026-08-09

Size and banner both lie. Use the **positive capability probe** in each row.

### `bin/simple` is the Rust bootstrap seed, not a self-hosted binary

CLAUDE.md says default tooling is the pure-Simple self-hosted binary. It is
not, today. Probe:

```bash
bin/simple --version 2>&1 | head -2
```

Observed:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

The binary prints its own disclaimer. `bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple`, and that file **is** a Rust
seed build. This is the likely root cause of the lint times above.

**There is currently no pure-Simple binary that can lint.** `bootstrap/stage{1,2,3}/simple`
(3.4 MB, all identical) are the staged pure-Simple compilers, and they expose
only `compile` and `native-build`:

```bash
$ bootstrap/stage3/simple lint --help
error: unknown command 'lint'      # exit 1 — fails closed, verified
```

So every lint today runs on the seed. `simple test` GREEN likewise does not
prove anything self-hosted — the only binary in the path is the seed.

### `bin/simple` is a symlink that other agents replace mid-session

**Verified live during this session:** `bin/release/x86_64-unknown-linux-gnu/simple`
changed from 29,573,408 bytes (Aug 8 12:14) to 58,940,120 bytes (Aug 9 04:30)
*between measurements in the same session*. The same lint that took 118.79s
took 125.60s afterwards, and the fixed startup went 11.70s → **42.97s**.

Always record binary identity alongside any timing:

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
```

A benchmark without this line is not reproducible here.

### `grep` is a wrapped ugrep honouring `.gitignore`

Confirmed by measurement today:

```bash
$ grep -rl "bootstrap seed only" src/ | wc -l           # 4
$ /usr/bin/grep -rl "bootstrap seed only" src/ | wc -l  # 17
```

A **4x undercount**, silently. `type grep` reports `grep is a function`. Use
`/usr/bin/grep` for any exhaustive scan or census.

### Profilers are unavailable — don't burn a session on them

- `perf record`: `/proc/sys/kernel/perf_event_paranoid` is **4**. Blocked.
- `gdb -p <pid>`: yama `ptrace_scope` is **1**, and gdb is a *sibling* of a
  shell-backgrounded process, not its parent, so attach fails with
  `ptrace: Inappropriate ioctl for device`. It also produces **zero stacks
  while still exiting 0** — a sampler built on it reports an empty profile
  rather than an error. `scripts/perf/sample-lint-stacks.shs` documents this
  dead end so the next agent doesn't rebuild it.

Use phase differencing instead (`lint` vs `fmt --check` vs a 24-byte file),
which is how the 10/20/70 split above was obtained without a profiler.

## 4. What did NOT help

- **Batching files into one lint invocation.** Superlinear; 2 files >600s vs
  119s for 1. Measured, rejected.
- **Chasing the env-var lexer state.** `SIMPLE_BOOTSTRAP_LEX_SOURCE` stores the
  whole source text in an environment variable and parser scopes save/restore
  it, which looks like the obvious quadratic culprit. It is **already off by
  default** — `lex_env_save_enabled` is `[false]` unless
  `SIMPLE_BOOTSTRAP_LEX_ENV_SAVE=1`. Not the bottleneck. Do not "fix" it
  expecting a speedup.

## 5. Open, not fixed

The 70% in the lint rules is untouched. The cache makes repeat runs free but a
cold lint of a real file is still ~2 minutes, and a first-time full-repo lint
is still impractical. Fixing that means making the rule passes cheaper inside
`lint_cli_source` (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`),
which needs a bootstrap rebuild to measure and was out of scope here.

## Bootstrap stage builds: the cache flag is the whole story (2026-08-17)

`bin/simple build bootstrap` hardcodes `--threads 1` and passes **no
`--cache-dir`** (`src/compiler_rust/driver/src/cli/commands/misc_commands.rs`,
both branches), so every invocation is a cold uncached recompile — measured 15+
minutes at 100% of one core without reaching codegen. Use
`scripts/bootstrap/bootstrap-from-scratch.sh`, which passes `--cache-dir`,
`--low-memory`, `--mode one-binary` and `--runtime-bundle core-c-bootstrap`.

Memory is the binding constraint on this host, not CPU: one `simple test`
process peaks ~3 GB and the stage worker holds ~2.9 GB, while `earlyoom` kills
`simple` preferentially at ~10% free. Bootstrap and broad test sweeps must
alternate. A native-build "timeout" should be checked against
`journalctl -u earlyoom` before it is believed.

## 6. Build-lane doctrine (2026-08-17)

- **One compile-build owner at a time.** Two concurrent stage-2 builds nearly
  triggered earlyoom on this host. Deconfliction: the script-driven run
  survives; ad-hoc builds yield, wait, or pin to a
  `build/phase_snapshots/` snapshot.
- **Phase builds never block on verification.** Sanity/tool-harness checks run
  in a parallel `nice`d lane (<=2 concurrent test processes) beside the build.
- Phase 2 can complete via dynload; the phase-4 relink then needs
  `--full-cli` / `--mode=one-binary` to produce the one-binary artifact.
- Pipeline traps observed 2026-08-17 (unfiled — file on next touch): silent
  stage-2 exit-1 with a 0-byte log under the transcribed sandbox env; a
  phantom `stage2-capability.log` reference; native-build has no keep-going
  flag, so sweeps run per-directory under `timeout`, per-file on crash.
## 6. Evidence hazards and lane priority (2026-08-17)

- **Silent green.** `bin/simple test <spec>` can emit ~1897 warning lines, no
  pass/fail line at all, and exit 0. Timing or verification runs on this
  command prove nothing unless an explicit results/count line is present;
  otherwise record INCONCLUSIVE and repro with `bin/simple run`. OPEN:
  `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`.
- **Memory priority.** The phase compiler build owns CPU/memory; test lanes
  throttle to 1 concurrent process when free RAM is low. Measured 2026-08-17
  (session-measured, unfiled): earlyoom killed `jobs=8` stage workers with ~14
  test lanes running, forcing the build to `jobs=2` — so a "slow build" number
  taken under parallel test load is a measurement of the load, not the build.
- **Run to the end.** Where the tooling can continue past an error, collect the
  full error census in one run rather than fixing one error per rebuild; the
  same applies to tool builds during phase verification (attempt all, even when
  some fail).

## Per-lane private build caches (2026-08-17)

Concurrent bootstrap lanes may drive DIFFERENT compiler binaries over the SAME
source tree. Both engines' native-build caches now carry a **lane** axis on top
of the compiler-identity axis they already had:

```bash
bin/simple native-build --cache-dir build/bootstrap/native_cache --cache-scope stage3 ...
SIMPLE_CACHE_SCOPE=stage3 bin/simple native-build --cache-dir ... ...   # same thing
```

- Unset ⇒ lane `default`; single-lane builds behave exactly as before.
- Entries are partitioned by a scope-derived **directory**, so a cross-scope
  lookup cannot name an out-of-scope entry — the miss is structural, not a hash
  comparison. The lane is folded into the object key as well.
- Each cache dir records its owner in a `.cache_scope` marker. Check ownership
  without running a compiler:

```bash
sh scripts/check/check-cache-scope-ownership.shs <cache-dir> <lane>   # PASS/FAIL/ERROR
sh scripts/check/check-cache-scope-ownership.shs --selftest
```

- `scripts/bootstrap/bootstrap-from-scratch.sh` now gives each stage
  `build/bootstrap/native_cache/<lane>/` and refuses, fail-closed, to build
  against a directory another lane owns.

Design: `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`.
Specs: `test/01_unit/compiler/cache/per_lane_cache_scope{,_prevention}_spec.spl`.
