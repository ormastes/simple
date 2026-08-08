# Lane REDEPLOY — self-hosted binary embedding current `src/compiler/**`

Date: 2026-07-27. Owner: lane REDEPLOY.
Master copy lives at `build/redeploy_logs/state.md`; a copy is placed at
`.spipe/redeploy_selfhost/state.md` (that directory was already wiped once
mid-session by another lane's sync — the known "sync sweeps agent scratch state"
hazard — so the lane-owned `build/` path is authoritative).

## Goal
Produce a working self-hosted binary embedding the current `src/compiler/**`
sources so two landed-but-unverified fixes can be confirmed or refuted:
- `src/compiler/10.frontend/core/interpreter/**` (lane PMS) — commit `f13728d790a`,
  files touched **2026-07-27 22:02**.
- `src/compiler/50.mir/mir_lowering_stmts.spl` (lane JITCA) — **UNCOMMITTED**
  working-copy change, touched **2026-07-27 22:04**.

## Survey (completed before any build)

### Binary inventory
| Path | Size | Date | What it actually is |
|---|---|---|---|
| `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` | 145 MB | Jul 27 22:06 | **Rust seed** — prints the "bootstrap seed only" WARNING. Deployed by another lane's `--deploy`. |
| `src/compiler_rust/target/bootstrap/simple` | 153 MB | Jul 27 06:57 | Rust bootstrap seed (canonical) |
| `build/native_probe/simple` | 48 MB | Jul 23 03:51 | stale; SIGSEGVs in native-build |
| `build/aggfix/x86_64-unknown-linux-gnu/simple` | 127 MB | Jul 27 13:18 | **pure-Simple stage2**, verified working — but built with `--entry bootstrap_main.spl`, so `run` is unsupported (`error: unknown command 'run'`) |
| `build/bootstrap/stage3/.../simple`, `build/coverage-bootstrap-586/...` | 127 MB | Jul 27 07:18–07:45 | same shape (bootstrap entry, no `run`) |

**Conclusion:** every self-hosted binary on disk is (a) older than the 22:02/22:04
fixes and (b) a `bootstrap_main.spl` entry that only supports `native-build`.
`run` requires an `--entry src/app/cli/main.spl` build.

### Route options considered
| Route | Command | Cost | Yields |
|---|---|---|---|
| **A — stage2 replay** | seed `native-build --entry src/app/cli/bootstrap_main.spl --mode dynload` | cheap with a warm cache | a self-hosted **compiler** embedding the new MIR lowering; can `native-build` the probes -> verifies JITCA. No `run`, so no interpreter probe. |
| **B — full-CLI** | `--entry src/app/cli/main.spl --mode one-binary` (`build_selfhost`, bootstrap-from-scratch.sh:598) | expensive; memory records ~65 GB RSS and SIGTERM at the 64 GB monitor cap | `run` / `test` -> PMS interpreter probe + specs |
| C — `bootstrap-from-scratch.sh --mode=dynload --deploy` | full wrapper (stages 1-5 + MCP handshake gate) | most expensive; `--deploy` is forbidden for this lane | superset of B |

**Chosen: A first, then B if resources allow.** A is the cheapest route that can
move either fix from "unverified" to "verified", and it validates the recipe and
cache reuse before paying for B. A never got a binary — see the blockers below.

### Warm cache selection
Only caches built with the **current** seed (Jul 27 06:57) are reusable: rebuilding
the seed changes `compiler_fingerprint` and invalidates every cached object.
- `build/bootstrap/native_cache`: 6,216 objs, newest Jul **26** 10:33 -> wrong seed.
- `build/aggfix/native-cache`: 1,372 objs, Jul 27 **13:17** -> same seed. **Selected**,
  copied (0.12 s) to lane-owned `build/redeploy_cache` so no other lane's cache is mutated.

### Resource situation (shared, heavily loaded box)
At start: load 20.9 / 47.0 / 54.9; 125 GB RAM, ~14 GB used, ~111 GB available; swap 6/7 GB.
Concurrently running, **not** owned by this lane and never touched:
- PID 1916460 `bootstrap-from-scratch.sh --full-bootstrap --full-cli --deploy`
- PID 2088280 `native-build --threads 24` (session `0cc17245`)
- `cargo build ... -p simple-driver`

Mitigations used: `nice -n 19`, `--low-memory`, `--threads 8`, 30 s RSS polling
(`build/redeploy_logs/rss.tsv`) with an automatic self-abort at 40 GB.

## Resource curve — measured, no hazard on this route
| Run | Wall | Peak RSS (this lane) | CPU | System used | Load1 range |
|---|---|---|---|---|---|
| 1 | 13 min | **0.8 GB** | ~1 core | 16–22 GB | 22–45 |
| 2 | 23 min | **0.2 GB** | ~1 core | 16–24 GB | 12–60 |
| 3 | see below | **0.2 GB** | ~1 core | 21–29 GB | 21–24 |

The 40 GB self-abort never triggered and was never approached. **The ~65 GB
stage4 balloon recorded in memory belongs to the `--mode one-binary --entry
main.spl` full-CLI build, not to this stage2 shape** — that distinction is the
useful resource finding here. The dominant cost of this route is *wall time in a
single-threaded frontend phase* (~13–20 min before codegen even starts), not memory.

## Baseline (current `bin/simple`, the Rust seed) — reproduced
| Probe | Result | Expected |
|---|---|---|
| `build/jitca_probe.spl` | `nested_compound=3`, `array_compound=10`, `onehop_compound=2` | `7 / 12 / 7` |
| `build/onehop_probe.spl` | `onehop=2`, `explicit=7` | `7 / 7` |
| `build/pms_probe.spl` (`SIMPLE_EXECUTION_MODE=interpreter`) | `d1 PASS 1`; `d2`, `d2acc`, `d3`, `selfroot` all `FAIL got=0`; then hard stop: `error: semantic: invalid assignment: deeply nested field access requires intermediate variables` | all rows PASS |

So the compound-assign defect is real and severe on the seed, and the seed's Rust
front end cannot even accept the deeper cases.

## Build log

### Run 1 — 22:43 -> 22:56 (13 min) — FAILED at link
```
/usr/bin/ld: build/native-objects-WVzh6v/mod_175.o: in function
  `hir__hir_lowering___Items__module_lowering__HirLowering.register_imported_symbol':
  undefined reference to `hir_registry_get'
/usr/bin/ld: build/native-objects-WVzh6v/mod_373.o: in function
  `backend__backend__interpreter_calls__InterpreterBackendImpl.try_call_builtin':
  undefined reference to `rt_file_is_regular_no_follow'
clang++: error: linker command failed with exit code 1
```

### BLOCKER 1 — `rt_file_is_regular_no_follow` missing from the runtime archives
- Added to `src/runtime/runtime.c:911` and `src/runtime/runtime.h:665` at
  **22:02:48 today** (commit `7f156785ed1`), declared `extern fn` in
  `src/compiler/70.backend/backend/interpreter_calls.spl:20` and
  `src/compiler/70.backend/sffi_minimal.spl:109`.
- `nm -g --defined-only` finds **0** definitions across all three prebuilt archives
  (`libsimple_runtime.a`, `libsimple_native_all.a`, `libsimple_compiler_backfill.a`),
  all dated Jul 27 **07:02** — i.e. ~15 h older than the C source.
- This is exactly the standing rule *"extern additions need bootstrap"*: a new
  `rt_*` requires `--full-bootstrap` (cargo rebuild of seed + runtime), which every
  cheap route deliberately skips.
- **Smallest repro:**
  `nm -g --defined-only src/compiler_rust/target/bootstrap/libsimple_runtime.a | grep rt_file_is_regular_no_follow`
  -> empty output.

### BLOCKER 2 — `hir_registry_get` is called but defined NOWHERE in the tree
- Call site: `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:463`
  `part_src = Some(hir_registry_get(part_hop.module_name))`
  (and `hir_registry_contains(...)` on line 462).
- `grep -rn 'fn hir_registry_get' src/` -> **no match**; same for `hir_registry_contains`.
  Neither function exists anywhere in `src/`.
- Introduced by commit `559832a135b` *"fix(hir): use contains_key + index reads for
  struct-valued dict lookups"*, landed **2026-07-27 21:59:55** — after the last
  successful self-hosted build (`build/aggfix/...`, 13:18), which is why no earlier
  binary exhibits it. Present in HEAD, so it is not a working-copy-only artifact.
- The call sits under `if imported_mod.functions.len() < 0:`, a condition that can
  never hold, so the emitted call is **unreachable dead code that still breaks the
  link**. A codegen/DCE gap compounds a source defect.
- **Smallest repro:** `grep -rn 'hir_registry_get' src/ --include=*.spl`
  -> exactly one call site, zero definitions.

### Workaround applied (entirely inside lane-owned paths; `src/**` untouched)
`build/redeploy_logs/link_shim.c` -> `link_shim.o`, merged via `ar r` into a
**private copy** of the runtime archive at `build/redeploy_runtime/` (top-level
files hardlinked from `src/compiler_rust/target/bootstrap`, with
`libsimple_runtime.a` copy-broken before `ar` so the shared archive cannot be
mutated). Verified: the original archive still reports 0 for `hir_registry_get`,
the private copy reports 2. The shim reimplements `rt_file_is_regular_no_follow`
with runtime.c's exact POSIX semantics (`lstat` + `S_ISREG`, length-aware for the
`(ptr, len)` SFFI signature) and nil-stubs the two dead `hir_registry_*` calls.

### Run 2 — 23:04 -> 23:27 (23 min) — FAILED at codegen, DIFFERENT error
```
FAILED FILES (1):
  src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl =>
  llvm codegen: semantic: llvm global load referenced undeclared symbol `depth`
Build failed: native-build aborted: 1 file(s) failed to compile
```
The link shim worked — run 2 got *past* both run-1 undefined symbols and reached a
new, later failure.

### BLOCKER 3 — `src/compiler/**` is being live-edited by a concurrent lane
`module_lowering.spl` has mtime **23:08:53**, i.e. it changed *while run 2 was in
flight* (launched 23:04). Session `0cc17245` is visibly cycling
`hir_module_lowering.spl.TEMPREPAIR` / `.orig` over that exact file, and
`git status` reports **255 modified files under `src/`**. The working copy is not a
stable, buildable input right now; each attempt samples a different tree, and a
~20 min build cannot outrun the edits.

### Run 3 — 23:29 onward, from a frozen snapshot
`git archive HEAD src examples/10_tooling | tar -x -C build/redeploy_src`
(13,848 `.spl` files), plus an overlay of the single uncommitted file this lane
must verify (`src/compiler/50.mir/mir_lowering_stmts.spl`, JITCA). This pins the
tree against concurrent edits while still containing **both** fixes under test:
PMS `f13728d790a` is committed and therefore in HEAD; JITCA is overlaid.
The snapshot's `module_lowering.spl` has 17 `depth` occurrences vs 21 in the
working copy, confirming the run-2 codegen failure lives in the concurrent lane's
uncommitted WIP rather than in HEAD.

### Run 4 — 23:45 -> 23:51 — FAILED, but now reproducible on a pinned tree
Run 3 failed with a *third* distinct error while still naming
`/home/ormastes/dev/pub/simple/src/compiler/...` in its diagnostics — proving
that **`native-build` resolves `src/compiler/**` relative to the process CWD, not
from `--source`**. Passing snapshot paths to `--source` is therefore not enough;
the build must be launched with `cd` into the snapshot. Run 4 does that and the
error message correctly names `build/redeploy_src/...`.

### BLOCKER 4 (the real, deterministic HEAD-level one) — incomplete refactor in `module_lowering.spl`
```
llvm codegen: semantic: llvm global load referenced undeclared symbol `depth`
```
- `register_glob_imported_symbols(imported_mod, imported_mod_name, import_span)`
  is declared at line 693 **with no `depth` parameter**, yet its body reads a free
  variable `depth` (line 761) and recurses into
  `self.register_glob_imported_symbols_depth(..., depth + 1)` (line 765) — a
  method that **does not exist**; only the 3-arg `register_glob_imported_symbols`
  is defined.
- So HEAD's `module_lowering.spl` references **four** identifiers that do not
  exist: `hir_registry_get`, `hir_registry_contains`,
  `register_glob_imported_symbols_depth`, and the free variable `depth`.
  The frontend accepts all of them; only codegen/link rejects them.
- **HEAD's `src/compiler` therefore does not build.** This is what session
  `0cc17245` is working around with its `.TEMPREPAIR` copies.
- Smallest repro (from a clean HEAD snapshot):
  `cd <snapshot> && <seed> native-build --backend llvm --source src/compiler --source src/lib --source src/app --entry-closure --entry src/app/cli/bootstrap_main.spl -o /tmp/x`

### Snapshot repair (build artifact only — `src/**` never modified)
Completed the refactor the way the author evidently intended, **in
`build/redeploy_src` only**: the real body becomes
`register_glob_imported_symbols_depth(..., depth: i64)` and the original 3-arg
entry point forwards with `depth = 0`. `git status` on the real
`src/compiler/20.hir/.../module_lowering.spl` shows only the *other* lane's
pre-existing modification; this lane never wrote to `src/`.

### Run 5 — 23:56 -> 00:05 — codegen PASSED, failed at link
The repair worked: `module_lowering.spl` compiled. New link errors revealed
`io__file_ops__file_read` / `io__file_ops__file_exists` missing — the closure
needs `src/app/io`, which `--source src/app/cli` excluded. Fixed by widening to
`--source src/app` (what the real bootstrap uses). The `rt_file_is_regular_no_follow`
shim was also added to `libsimple_native_all.a` as well as `libsimple_runtime.a`.

### Run 6 — 00:08 -> 00:11 — **SUCCESS**
```
Build complete: 8 compiled, 683 cached, 0 failed
  Binary: build/redeploy_out/simple_stage2 (123960 KB)
  Time: 82.1s compile + 119.7s link = 201.7s total
```
**Artifact: `/home/ormastes/dev/pub/simple/build/redeploy_out/simple_stage2`**
(126,935,632 bytes, Jul 28 00:11). `bin/simple` and `bin/release/**` were never
touched.

## Provenance — the binary really does embed the JITCA fix
Because 683 of 691 modules came from cache, this had to be proved, not assumed:
- `compound_field_mir_type` and `lower_compound_combine` occur **0 times in
  HEAD's** `mir_lowering_stmts.spl` and 2 / 5 times in the uncommitted JITCA version.
- `nm -a build/redeploy_out/simple_stage2 | grep -c compound_field_mir_type` -> **1**.
So a symbol that exists only in the JITCA fix is present in the linked binary.
The PMS interpreter fix (`f13728d790a`) is committed and therefore in the HEAD snapshot.

## VERIFICATION TABLE

Compiled with the new self-hosted `simple_stage2` (`native-build`, llvm backend),
then executed directly — no session daemon, no `simple test`, so the stale-daemon
trap does not apply.

| Probe | Expected | Rust seed (baseline) | **New self-hosted binary** | Verdict |
|---|---|---|---|---|
| `jitca_probe` nested `c.mid.inner.n += 4; += 3` | 7 | 3 | **3** | **UNCHANGED — fix refuted** |
| `jitca_probe` array `arr[1] += 10` on `[1,2,3]` | 12 | 10 | **10** | **UNCHANGED — fix refuted** |
| `jitca_probe` one-hop `s.n += 2` (n=5) | 7 | 2 | **2** | **UNCHANGED — fix refuted** |
| `jit_compound_probe` (all three rows) | 7 / 12 / 7 | 3 / 10 / 2 | **3 / 10 / 2** | **UNCHANGED** |
| `onehop_probe` `s.n += 2` | 7 | 2 | **2** | **UNCHANGED** |
| `onehop_probe` `t.n = t.n + 2` (explicit) | 7 | 7 | **7** | PASS (control) |
| `pms_probe` (interpreter) | all PASS | `d2/d2acc/d3/selfroot FAIL got=0` + hard semantic error | **NOT REACHED** — needs `run`; stage2 entry has no `run` command | pending full-CLI build |
| `compound_assign_place_spec.spl` | — | — | **NOT REACHED** — needs `simple test` | pending full-CLI build |
| `two_hop_field_method_mutation_spec.spl` | — | — | **NOT REACHED** | pending full-CLI build |
| `duplicate_owner_spec.spl`, `ds_service_spec.spl` | — | — | **NOT REACHED** | pending full-CLI build |

### What this means
The JITCA fix is **embedded and ineffective on the native codegen path**. The
arithmetic is diagnostic: `s.n += 2` with `n == 5` yields exactly `2`, and
`n += 4; n += 3` yields exactly `3` — i.e. `0 <op> rhs` every time. The
read-modify-write the fix adds *is* being emitted, but the value it reads back is
**0**, not the field's current contents. So the defect is not "the read is
missing" (what the fix addressed) but "the read returns zero" — the emitted
`emit_get_field(mir_operand_copy(receiver), field_index, ...)` does not observe the
live field. The control row proves the field itself is fine: the explicit
`t.n = t.n + 2` spelling reads 5 and yields 7 through the very same struct.
Next investigator should look at `mir_operand_copy(receiver)` / `resolve_field_index`
rather than at whether `op` is threaded through `lower_assign`.

### BLOCKER 5 — the Rust seed was clobbered mid-session
At **00:14:37** another lane's cargo build replaced
`src/compiler_rust/target/bootstrap/simple`: 153,761,080 bytes
(md5 `bf218c16…`, llvm-capable) -> **31,728,808 bytes** (md5 `c607db19…`), built
**without `--features llvm``. The next build died instantly with
`error: native backend 'llvm' is not available in this build`.
This lane survived only because `build/redeploy_runtime/simple` is a **hardlink**
made before the clobber and still resolves to the original inode (md5 verified
identical). All subsequent builds were re-pointed at that preserved copy.
Recurrence of the known "seed-clobbered again" landmine; hardlinking the seed into
a lane-owned directory at the start is a cheap and effective guard.
