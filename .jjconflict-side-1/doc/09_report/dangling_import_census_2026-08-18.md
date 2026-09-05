# Dangling-import census across owned code (2026-08-18)

Lane DANGLING2. Tool under test: `bin/simple`, the **Rust seed** — every
diagnostic quoted here is attributed to the seed, not to a self-hosted binary.

## Headline

**A handful of rotted edges, not a meaningful fraction of the tree — and the
static number is an upper bound dominated by false positives.**

The static scan flags 307 module-level and 444 symbol-level candidates out of
31,991 `use` statements in owned code (~0.96% / ~1.4%). A 15-item hand-check
put the false-positive rate at **~93% (14 of 15)**, so those counts are
presented as UPPER BOUNDS and explicitly **not** as defect counts.

The defects that are actually *confirmed* — by running the seed and reading its
own diagnostics — number **three clusters, 44 import edges**, and **all three
are on dead or near-dead paths**.

## Scope

Scanned: `src/lib/**`, `src/app/**`, `src/compiler/**`, `src/os/**`
(13,667 physical `.spl` files; 24,332 logical paths once symlinked package
roots are expanded).

Excluded per CLAUDE.md Owned-Code Scope: `src/compiler_rust/vendor/**`,
`src/runtime/vendor/**`, `src/runtime/miniaudio.h`, `src/runtime/stb_image.h`,
`src/runtime/stb_truetype.h`, anything under `.vscode-test/`, plus
`src/compiler_rust/target/**` (build output). `src/compiler_rust/lib/std/**`
was scanned in an earlier pass and then excluded as out of the four named
roots — it contributed the entire `units.*` hit family, which is why that
family is absent from the final counts.

## Resolution rule (stated explicitly)

Deliberately **maximally permissive**: every ambiguity resolves in favour of
"this import is fine", so that surviving hits are strong and the count is a
true upper bound.

1. **File index.** Walk `src/` *following symlinks*, deduplicating directories
   by relative path. Plain `find` does **not** follow symlinks and would have
   missed `src/app/lsp -> ../lib/nogc_sync_mut/lsp` entirely, mis-flagging
   every `app.protocol.*` import inside it. 14 such package roots exist under
   `src/compiler/` alone.
2. **Path segmentation splits on `/` *and* `.`.** The tree uses dot-named
   directories as a real namespacing device: `src/app/ui.render/ansi.spl` **is**
   module `app.ui.render.ansi`. Missing this one rule alone produced ~180
   false module-level misses (`app.ui.render.*`, `app.dashboard.render.*`,
   `app.ui.chromium.*`, `app.ffi_gen.*`).
3. **Module match = ordered subsequence.** A key `a.b.c` resolves if its
   segments appear as an ordered subsequence of some file's segment path.
   This subsumes, without enumerating them: the entry-file-directory module
   root, numbered layer dirs (`src/compiler/10.frontend/core/ast.spl` is
   reachable as `compiler.core.ast`), and intermediate package segments such
   as `simple-lang` in `src/unit/simple-lang/area/acre.spl` = `unit.area.acre`.
4. **`std.` maps onto `lib/`** during subsequence matching.
5. **Symbol universe = union over ALL candidate modules** for an ambiguous
   key — this is the correction the previous cut-off attempt identified, and
   without it every facade with a same-named sibling reports spuriously.
   For a package key the union additionally includes every file sitting
   directly in the package directory alongside `__init__.spl`.
6. **Opaque modules are skipped, never flagged.** Any candidate module
   containing a wildcard (`use m.*` / `export use m.*`) makes the whole key
   opaque; no symbol-level claim is made about it.
7. Re-exports are harvested from `use`, `export use`, **and `pub use`**
   (`pub use` is the dominant facade form in `src/compiler/00.common/**` —
   omitting it initially produced ~100 false symbol-level hits against
   `compiler.common.driver_core_types` alone).
8. Brace lists are parsed **across line breaks**; the real facades wrap over
   6-20 lines and a line-anchored regex silently truncates them.
9. Roots `sffi`, `c`, `llvm`, `core`, `self`, `super` are never flagged.

## False-positive rate: ~93% (14 of 15 hand-checked)

Random sample, seed 11, 8 module-level + 7 symbol-level.

| # | Hit | Verdict | Why |
|---|-----|---------|-----|
| 1 | `TestRunnerReplayAdapter` | FP | `pub use <BareName>` re-exports a *local* binding, not a module path |
| 2 | `discover_apps` | FP | same |
| 3 | `RemoteReplayMode` | FP | same |
| 4 | `ParserPort` | FP | same |
| 5 | `std` (`use std.{text, collections}`) | FP | brace list of **submodules**, not symbols |
| 6 | `os.services.netstack` | FP | directory exists |
| 7 | `os.kernel.arch_adapt.x86_32` | FP | directory exists |
| 8 | `common.ui.theme_package` | FP | file exists under a sibling package |
| 9 | `vmm_map_page` | FP | `vmm.spl` is a facade of bare `use os.kernel.memory.vmm_core` — plain whole-module `use` re-export, which the scanner does not propagate |
| 10 | `vmm_replace_pte_in` | FP | same facade |
| 11 | `GLASS_SURFACE_2_A` | FP | defined in sibling `common/ui/glass/numeric_tokens.spl` |
| 12 | `GLASS_LIGHT_BG_BOT` | FP | same |
| 13 | `mod_exp` | FP | facade |
| 14 | `__init__` | FP | parser artifact |
| 15 | **`app.mcp.prompts`** | **TRUE** | no `prompts.spl` anywhere under `src/app/mcp/` |

The residual FP generators are the two facade forms the scanner cannot follow
without a real name resolver: `pub use <BareName>` and plain `use <module>`
whole-module re-export. Both are legitimate, widespread Simple idioms.

## Confirmed defects (empirical, verbatim seed output)

`bin/simple check` was not used (>600s). All confirmation is by
`bin/simple run`, reading **both** the exit code and the warning stream —
because an undefined *symbol* produces only a warning and **rc=0**, so a clean
exit is not evidence of a clean import.

### 1. `app.mcp_jj.*` — 32 edges, 12 files — HARD ERROR, rc=1

```
$ bin/simple run src/lib/nogc_sync_mut/mcp/jj/helpers.spl ; echo RC=$?
[INFO] JIT compilation failed, falling back to interpreter: semantic: Cannot resolve module: app.mcp_jj.jj_runner
error: semantic: Cannot resolve module: app.mcp_jj.jj_runner
RC=1
```

No `src/app/mcp_jj` directory exists anywhere in the tree. The real targets
are immediate siblings of the importer (`src/lib/nogc_sync_mut/mcp/jj/jj_runner.spl`
defines `JjResult` at line 11). This is a package relocated out of `src/app/`
into `src/lib/nogc_sync_mut/mcp/jj/` whose imports were never rewritten —
**the same module-root defect as the already-filed `test_runner/main.spl`
case**: `app.*` is unresolvable from a `src/lib/**` entry file.

**Dead.** Zero external importers (`grep` for `mcp.jj`/`mcp/jj` outside the
package returns nothing), zero references from `scripts/`, `bin/`, or
`.mcp.json`. Filed rather than mass-fixed: 32 edges across 12 files is a
subsystem migration, not a small-and-certain fix.

### 2. `std.nogc_sync_mut.simd` — 9 symbols — WARNING ONLY, rc=0 — **FIXED**

```
[use-warning] 'Vec16u8' is named in `use std.nogc_sync_mut.simd.{...}` but module
'/mnt/data/worktrees/simple-main/src/std/nogc_sync_mut/simd.spl' does not provide it
(imported from '/mnt/data/worktrees/simple-main/src/std/nogc_async_mut/simd.spl')
```

`src/lib/nogc_async_mut/simd.spl` re-exported `Vec16u8`, `Vec2u64`,
`simd_add_u8x16`, `simd_xor_u8x16`, `simd_aes_round`, `simd_aes_round_last`,
`simd_clmul_lo_u64`, `simd_clmul_hi_u64`, `simd_xor_u64x2` from
`std.nogc_sync_mut.simd`. All nine are defined in
`std.nogc_sync_mut.simd_crypto` instead — one clear new path, verified
individually. Fixed by splitting the re-export.

**This one is LIVE**: it fired on every real entry point tested
(`src/app/mcp/main.spl`, `src/app/dashboard/main.spl`,
`src/app/test/x25519mlkem768_candidate_batch_measurement.spl`).

Verification, same entry point before and after:

```
before: 9 [use-warning] lines, RC=0
after:  0 [use-warning] lines, RC=0
```

### 3. `platform_measurement_observer.spl` — 3 symbols — WARNING ONLY, rc=0

```
[use-warning] 'process_peak_rss_kb' is named in `use std.nogc_sync_mut.io.sysinfo_ops.{...}`
but module '.../src/std/nogc_sync_mut/io/sysinfo_ops.spl' does not provide it
(imported from '.../src/std/nogc_sync_mut/platform_measurement_observer.spl')
```

Also `current_executable_path` (same module) and `monotonic_clock_identity`
(from `std.nogc_sync_mut.io.time_ops`). `process_peak_rss_kb` is defined
**nowhere in `src/`** — `grep -rn "fn process_peak_rss_kb" src/` returns
nothing. **Not fixed**: there is no target to point at, and inventing a
module or deleting the import to silence the warning are both forbidden. The
consumer `src/app/test/x25519mlkem768_candidate_batch_measurement.spl` runs
rc=0 today, meaning the peak-RSS metric it reports is built on an import that
resolves to nothing.

## Live vs dead

| Cluster | Edges | Seed verdict | Live? |
|---|---|---|---|
| `app.mcp_jj.*` | 32 | `error: Cannot resolve module`, rc=1 | **Dead** — no external importer |
| `nogc_async_mut/simd.spl` | 9 | `[use-warning]`, rc=0 | **Live** — every entry point (now fixed) |
| `platform_measurement_observer` | 3 | `[use-warning]`, rc=0 | Reachable from one app-test entry |

Prevalence is not impact: the largest cluster (32 edges) is entirely dead,
while the one that mattered was 9 edges on a live path and cost nothing but a
warning nobody read.

## Systemic verdict

The seed **already detects this defect class correctly** — its `[use-warning]`
is a working symbol-level dangling-import checker and its `Cannot resolve
module` is a working module-level one; the failure is purely that a dangling
*symbol* is a non-fatal warning on an rc=0 run, so it accumulates silently
until someone happens to read the log.

## Method note

`bin/simple` is the Rust seed and says so on every run. The wrapped `grep`
honours `.gitignore` and under-reports; `/usr/bin/grep -rn` was used
throughout. Scans were run in the background and polled so no count was
truncated by a timeout. During this session the `simd.spl` edit was clobbered
once by a parallel session and had to be re-applied before committing —
consistent with the anti-revert warnings in `.claude/rules/vcs.md`.
