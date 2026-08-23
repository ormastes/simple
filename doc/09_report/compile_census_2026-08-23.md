# Compile-Everything Census — 2026-08-23

**Scope:** every `.spl` file under `src/` at `origin/main` = `619a9a616ad`, excluding
vendored/third-party per CLAUDE.md Owned-Code Scope (`src/compiler_rust/vendor/**`,
`src/runtime/vendor/**`). **15,212 files, 15,212 rows — zero files missing a row**
(verified by `comm` of the file list against the TSV path column; this is a measured
zero, not a zero-by-absence).

**Raw TSV:** `/mnt/data/worktrees/compilesweep-2/sweep/seed.tsv`
(5 cols: `path`, `rc`, `last step N/6`, `artifact bytes` (`-1` = no artifact), `first error line`).
Supporting: `sweep/families.txt` (coarse), `sweep/classes.txt` (656 normalized signatures),
`sweep/classify.sh`, `sweep/run_one.sh`, `sweep/files.txt`.

## Method (stated exactly)

Compiler = the **Rust seed**, rebuilt from this commit
(`cargo build --release --bin simple` in `src/compiler_rust`, deployed to
`bin/release/x86_64-unknown-linux-gnu/simple`; the seed prints its own
"bootstrap seed only" warning on every run, which the classifier strips).

Invocation, one process per file, run **from the worktree root** (paths are repo-relative):

```
timeout 300 bin/simple compile --format=smf -o <tmp>/o.smf <file>
```

`SIMPLE_TIMEOUT_SECONDS=0` exported; `xargs -P 6` (box load average was 20–31 from other
lanes, 32 cores — deliberately not saturated). Wall time ≈ 50 min.

### Measurement traps checked

- **cwd trap (hit and fixed).** A first probe run from `sweep/` returned `rc=1` for
  **40/40 files in 1.0 s** — every row was `io: Cannot read ... (os error 2)`. A sweep
  that reports 100% failure instantly is not a compiler result. All reported numbers are
  from runs rooted at the worktree root.
- **Success that did nothing.** Every row records the output artifact size.
  `rc=0 && artifact<=0`: **0 rows** (checked, genuinely zero). `rc!=0 && artifact>0`:
  **0 rows**. So `rc=0` really does mean "an SMF was emitted".
- **Non-vacuity.** Row count equals file count exactly; no class below is inferred from
  an empty counter.
- **Anchor.** The prior (dead) lane's complete sweep at `371825c23db` gave 9,499 fail /
  5,724 OK = 62.4% fail. This lane gives 62.4% fail. The two lanes agree, so the 14
  changed Rust-seed files between the commits did not move the aggregate.

## rc distribution

| rc | meaning under this harness | count |
|---|---|---|
| 0 | compiled, SMF emitted | 5,721 (37.6%) |
| 1 | compiler reported a diagnostic and exited | 9,491 (62.4%) |
| 124 | timeout (300 s) | **0** |
| 139 | SEGV | **0** |
| 137 / 143 | SIGKILL/SIGTERM (earlyoom memory pressure — not a compiler defect) | **0** |

Harness note: this lane uses plain `timeout 300` (no `-s KILL`), so a timeout would
surface as **124**, cleanly separable from an earlyoom **137**. The prior lane used
`timeout -s KILL`, which conflates the two — its `137`s are ambiguous and are not
carried forward here.

**No crashes and no hangs on the whole tree.** The prior lane's `stage2.tsv` (606 of
4,515 rows, a *different* compiler — a stage2 self-hosted binary, on a dead lane) is
full of `rc=139` SEGVs. Those belong to the stage2 binary, not to the seed, and are
**not** merged into any number above.

## Ranked error classes (families)

| # | class | files | share | representative |
|---|---|---|---|---|
| 1 | semantic: undefined identifier | 5,782 | 38.0% | `src/app/browser/gui_window.spl` |
| — | *(OK — no error)* | *5,721* | *37.6%* | `src/app/any_audit/classify.spl` |
| 2 | semantic: needs-interpreter constructs, not standalone-SMF-able | 1,891 | 12.4% | `src/app/any_audit/main.spl` |
| 3 | semantic: no lowerable `main` entry point | 604 | 4.0% | `src/app/dashboard.render/colors.spl` |
| 4 | lint rule violation (compile is gated by lint) | 396 | 2.6% | `src/app/game.breakout/game.spl` |
| 5 | parse error | 347 | 2.3% | `src/app/cli/_CliMain/main_and_help.spl` |
| 6 | HIR lowering: unsupported feature | 277 | 1.8% | `src/app/ffi_gen/test_intern_only.spl` |
| 7 | codegen failure | 106 | 0.7% | `src/app/debug/interpreter_backend.spl` |
| 8 | semantic: other | 49 | 0.3% | `src/app/audit/ffi_usage.spl` |
| 9 | MIR lowering: unsupported HIR construct | 39 | 0.3% | `src/app/dap/adapter/local.spl` |

Sums to 15,212.

### Class 1 decomposed — one root defect dominates the tree

332 distinct undefined symbols; counts are **first-error-only**, so each is "files blocked
by", not independent defects.

| symbol | files | representative |
|---|---|---|
| `runtime_file_rename` | 3,065 | `src/app/browser/gui_window.spl` |
| `string_core_text_to_bytes` | 575 | `src/app/build/targets/action_identity.spl` |
| `panic` | 555 | `src/app/arm64_auth_contract/main.spl` |
| `wrap_text` | 111 | `src/app/mcpgdb/debug_rules.spl` |
| `char_code` | 93 | `src/app/dashboard.views/status.spl` |
| `Array` | 70 | `src/compiler_rust/lib/std/src/host/async_gc_immut/net/http.spl` |
| `IoError` | 62 | `src/compiler_rust/lib/std/src/alloc/__init__.spl` |
| `unsafe` | 59 | `src/app/test/torch_cuda_optimizer_probe.spl` |

**Headline: the top two symbols are both renamed-import aliases, and they are the same
bug.** Both are introduced by `use ... as ALIAS` in the stdlib:

- `src/lib/nogc_sync_mut/io/file_ops.spl:233` — `use std.io_runtime.{file_rename as runtime_file_rename}`, used at line 236
- `src/lib/common/crypto/sha256.spl:19` and `src/lib/common/crypto/types.spl:5` — `use std.common.string_core.{text_to_bytes as string_core_text_to_bytes}`

The seed's resolver does not register the alias, so any file transitively importing
`std` io or crypto dies at that alias. That is **3,640 files = 23.9% of the whole tree**
blocked by one resolver gap — nearly a quarter of the census, and the single highest-value
fix visible in this data. (Census only; nothing was fixed in this lane.)

## Per-subtree success rate

| subtree | files | OK | OK % |
|---|---|---|---|
| `src/lib` | 7,868 | 3,124 | 39.7% |
| `src/app` | 2,692 | 1,010 | 37.5% |
| `src/compiler` | 1,812 | 510 | 28.1% |
| `src/os` | 1,681 | 540 | 32.1% |
| `src/compiler_rust` (non-vendor `.spl`) | 725 | 179 | 24.7% |
| `src/unit` | 360 | 329 | 91.4% |
| `src/i18n` | 29 | 2 | 6.9% |
| `src/runtime` | 20 | 12 | 60.0% |
| `src/type` | 13 | 13 | 100% |
| `src/verification` | 8 | 0 | 0% |
| `src/tooling` | 2 | 2 | 100% |
| `src/hardware` | 1 | 0 | 0% |
| `src/generated` | 1 | 0 | 0% |

## Known limits of this census

- **Per-file standalone compile is not the normal build mode.** Classes 2 and 3
  (2,495 files, 16.4%) are largely *expected* for a non-entry module: a library file has
  no `main`, and `--format=smf` demands a standalone artifact. They are catalogued as
  distinct classes rather than silently discounted, but they are the weakest evidence of
  a defect here.
- Classes 1, 5, 6, 7, 9 (6,551 files) are compiler-side gaps that a per-file compile is a
  fair probe of.
- Class 4 (396) is a lint policy gate firing inside `compile`, not a compile failure.
- Only the **first** diagnostic per file is recorded; a fixed root cause will reveal
  further errors behind it.
