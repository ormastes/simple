# Showcase matrix — evidence-based census (2026-07-30)

Purpose: re-measure the top line after many hours in blockers. **No cell
count here is taken from a report that claims success; every row states
what artifact would verify it and whether that artifact exists on THIS
host at THIS tip.**

Tip audited: `be0da59cfe3c47354ab6f47df2b3e5fd86a4e77d`.
Host: Linux x86_64, load 25-54, `kill_simple_monitor` daemon live.

## Authoritative cell definition

`doc/09_report/showcase_matrix_fresh_evidence_2026-07-25.md` (lines
11-19) — the only file in the repo that enumerates exactly 7 cells as a
matrix with per-cell verdicts and evidence. Cell names below are
**verbatim** from its table; no gate script enumerates the 7 cells, so
this report is the definition of record (PROVED by reading it).

## Finding that invalidates every prior cell count (PROVED)

That definition's evidence was collected with
`bin/release/aarch64-apple-darwin-macho/simple` — a **macOS aarch64**
binary — from main `4ed680f5`. On this host:

- that binary path **does not exist** (`bin/release/` holds only
  `linux-x86_64`, `x86_64-unknown-linux-gnu`, `riscv64-unknown-simpleos`,
  `x86_64-unknown-simpleos`);
- `4ed680f5` is **1,898 commits** behind the audited tip
  (`git rev-list --count 4ed680f5..be0da59c`).

Therefore **no cell is GREEN on this host today** — not even the two
long-standing "PASS" cells. They are CLAIMED: the artifacts are real but
were produced on another platform, 1,898 commits ago. "2/7 green" is not
a statement about this host at this tip.

## Census

| # | Cell (verbatim) | Lane | Status | Evidence / why | Settling command |
|---|---|---|---|---|---|
| 1 | `widget × headless` | interpreted | **CLAIMED** | 640x480 P6 PPM, 921,600/921,600 nonzero px, sha256-verified font raster — but macOS aarch64 binary @ `4ed680f5`, 1,898 commits stale; no artifact on this host. PROVED stale, INFERRED still-passing | re-run the widget headless render on a Linux-built `bin/simple` and re-capture the PPM + nonzero/checksum counts |
| 2 | `2D × headless` | interpreted | **CLAIMED** | `graphics_2d_nonzero=76789/76800`, `checksum=1108808631`, 103s CPU (rerun 2026-07-26) — same stale-platform caveat. PROVED stale, INFERRED still-passing | re-run the 320x240 software offscreen 2D render on this host; compare `graphics_2d_nonzero` + `checksum` to 76789/76800 and 1108808631 |
| 3 | `web × headless` | interpreted | **BLOCKED** (honest FAIL) | `status=fail reason=blank-or-uniform pixels=172800 nonzero=172800 checksum=1322071898`, deterministic. Named blocker: 10s paint budget expires under the interpreter so only the canvas background paints — `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md`. Coordinator notes module compile alone exceeded 48 min under load and the JIT path is one `text.from_any` fix from a real measurement. PROVED (blocker doc + verdict both tracked) | land the `text.from_any` fix, then run the web headless render on the COMPILED lane (the cell is explicitly compiled-lane-gated) |
| 4 | `widget × host-WM` | window | **UNKNOWN** (was BLOCKED; named blocker is STALE) | See "Host-WM" below — the documented blocker no longer reproduces. No window artifact has ever been produced for this cell on this host. PROVED that the blocker is gone; status beyond that never measured | `scripts/check/check-linux-hosted-wm-live-window-evidence.shs` (spawns Xvfb, `WINIT_UNIX_BACKEND=x11`) and capture `window_id` + a non-uniform screenshot |
| 5 | `2D × host-WM` | window | **UNKNOWN** (same) | Same stale blocker. Ancillary evidence exists but is NOT this cell: `check-hosted-wm-capture-evidence.shs` passed an *offscreen synthetic* WM-chrome capture (16x16 crop, 90/256 non-background px, checksum 473142143) — synthetic offscreen chrome is not a live window | same gate as #4, 2D wrapper |
| 6 | `web × host-WM` | window | **UNKNOWN** (same) | Same stale blocker; also inherits #3's paint-budget problem once a window opens | same gate as #4, web wrapper |
| 7 | `SimpleOS-WM × QEMU` | native-build+boot | **BLOCKED** | The definition itself records **UNVERIFIED**, explicitly rejecting an unretained local pass as non-acceptance evidence; latest canonical tracked report (`simpleos_wm_fullscreen_evidence_2026-07-24.md`) is **FAIL** `reason=wm-simple-web-build-failed`. Current named blocker: guest boots then hits a **missing-vtable `ud2` in `engine2d_draw_ir_render_batch_embedded`**. Open font anomaly: `has_ttf=0` on 117/118 metric resolves (`pointer_release_font_metrics_hang_2026-07-26.md`). PROVED (all tracked) | fix the missing-vtable `ud2`, then `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` for serial transcript + fullscreen capture |

**Scoreboard on this host at this tip: 0 GREEN, 2 CLAIMED, 2 BLOCKED, 3 UNKNOWN.**
(The two BLOCKED are #3 and #7; the three UNKNOWN are the host-WM row.)

## The two load-bearing claims, checked

### (a) "Three host-WM cells unblocked, real window rendered at `54ed5df7c8b`" — CLAIMED (real prior evidence, no artifact here)

- `54ed5df7c8b` is, by its subject line,
  `fix(seed-interp): register rt_string_to_int + rt_raw_i64_to_string in
  EXTERN_DISPATCH` (2026-07-28) — PROVED by `git log -1`. Campaign memory
  records that fix's *effect* as unblocking the host-WM cells, with
  captured evidence (`WIN 2097154`, `windows=1 taskbar_items=1`, 550s
  under Xvfb). Those are two linked facts, not a mislabeled commit: the
  hash is the EXTERN_DISPATCH fix AND the window render is real prior
  evidence. **The status point stands regardless: no artifact verifies it
  on THIS host at THIS tip, so the correct status is CLAIMED** — the
  earlier evidence is not discarded, it is simply not re-verified here.
- The *real* named blocker for all three cells — a semantic-phase
  co-import failure where importing `common.ui.wm_app_process_contract`
  together with `std.nogc_sync_mut.ui.gui_renderer` gave
  `error: semantic: Cannot resolve module` — is recorded **OPEN** in
  `doc/08_tracking/bug/co_import_makes_module_unresolvable_wm_contract_gui_renderer_2026-07-27.md`
  (mtime Jul 27 23:59).
- **That blocker no longer reproduces (PROVED).** Co-importing both
  modules at this tip runs clean: `rc=0`, zero `Cannot resolve module`
  occurrences, prints `COIMPORT_OK`, cold-cache (`.simple` removed) as
  well as warm.

So the correct statement is neither "unblocked with a window rendered"
nor "blocked": the blocker is **gone**, and the cells are **UNKNOWN**
because no live-window artifact was ever produced for them here. The
next action on these three is cheap and well-defined (gate #4 above),
which is the actionable half of this census.

### (b) "widget and 2D headless are the long-standing 2/7 green" — CLAIMED, not GREEN

Both cells' artifacts are real and internally consistent, but were
produced on a macOS aarch64 binary 1,898 commits ago and cannot be
verified on this host without a re-run. Per the brief I did not force a
green: each re-run is a multi-minute render under load 25-54 (the 2D
cell already has a recorded 40+ minute FAIL at a perf boundary), so
these stay CLAIMED with the settling commands stated above.

## Incidental finding (new, not previously tracked)

The co-import probe surfaced a **Cranelift JIT bail on this path**:
`Module error: function '_sorted_timer_stats' creates a lambda/closure`,
which silently falls back to the interpreter. Relevant to the host-WM
cells because the interpreter fallback is exactly what makes #3's paint
budget expire; worth a look before measuring #4-#6 for performance
rather than mere window existence. PROVED (observed in the probe's
stderr); impact on the cells INFERRED.

## Method note

Cheap verifications only, per the brief. The one gate-scale reproduction
I ran (co-import, documented at ~14s) was chosen because it settles
three cells at once; it completed in under a second. No expensive render
or QEMU gate was run to manufacture a green, and every unverified row
carries the exact command that would settle it.

## Host-WM gate run (2026-07-30) — cells stay BLOCKED, now on a PROVISIONING gap

`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` (51KB,
modified 2026-07-30 02:12) was run to settle cells #4-#6. **It cannot
reach a pass on this host.** The gate is a provenance-attesting gate:
every rejection below is an anti-fabrication guard, which is exactly why
it cannot be cheaply faked — and why the prior macOS evidence came from a
machine that had the assets.

Gate contract (PROVED by reading): entry `src/os/hosted/hosted_entry.spl`
native-built with `SIMPLE_LIB=src`; writes
`build/linux-hosted-wm-live-window-evidence/` (`report.md`, `hosted-wm`,
`build.log`, window PNG, framebuffer PPM, snapshot); ~25 sub-assertions
(`framebuffer`, `live_window`, `glyph_crop`, `focus`, `pointer`,
`keyboard`, `text`, `input_receipt`, `semantic`, `replay_rejection`,
`move`, `maximize`, `restore`, deliberate-red calibration, ...) reduced
to `linux_hosted_wm_live_window_status=pass|fail`. Budgets:
`LINUX_HOSTED_WM_LIVE_TIMEOUT_SECS` default 60 (window wait),
`LINUX_HOSTED_WM_BUILD_TIMEOUT_SECS` default 600 (native-build) — so a
genuine full run is ~10 min, consistent with the 550s prior evidence.

Wall chain, each PROVED by execution (every attempt ≤1s, so no timeout or
kill-daemon interaction was possible; 4 daemon PIDs were live throughout):

| # | `reason=` | Meaning | Satisfiable here? |
|---|---|---|---|
| 1 | `source-provenance-unavailable` | requires clean `src/os`+`src/lib`; the shared working copy had **29** uncommitted changes | YES — re-run in a clean worktree; `source_provenance_status=pass` confirmed |
| 2 | `explicit-simple-bin-required` | `SIMPLE_BIN` must be passed explicitly | YES |
| 3 | `rust-seed-forbidden` | rejects the Rust seed (correct per the pure-Simple standing rule) | YES — `build/redeploy_out/simple_stage2` (pure-Simple lineage) accepted |
| 4 | `runtime-provider-explicit-required` | `SIMPLE_WM_RUNTIME_LIB` must be passed explicitly | YES |
| 5 | `runtime-provider-sha` | caller must attest the provider's sha256 (`SIMPLE_WM_RUNTIME_LIB_SHA256`; no hardcoded pin) | YES — attesting the true sha is intended usage, not a bypass |
| 6 | `runtime-provider-bootstrap-forbidden` | the **bootstrap** runtime `.so` is explicitly rejected | **NO** — the only self-hosted-lineage runtime lib on this host is the bootstrap one |
| 7 | `pinned-font-asset-invalid` (unreached, but unreachable-to-pass) | hardcoded pin `FONT_ASSET_SHA256=2cb2adb3…` on `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf` | **NO** — `assets/fonts/` holds **0 tracked files at tip** and the directory is absent from the working tree; the asset is not in the repo at all |

**Verdict: cells #4-#6 remain BLOCKED — but the blocker is now precisely
characterized and it is NOT a WM defect, NOT the co-import defect (proved
gone above), and NOT Xvfb.** It is an **asset/runtime-provider
provisioning gap**: two independent, deliberately-pinned prerequisites
(a non-bootstrap self-hosted runtime provider `.so`; the pinned font
asset) are simply not present on this host. Status vocabulary updated
from UNKNOWN to BLOCKED for #4-#6 on that basis.

Not fixed here, per brief: provisioning a pinned font asset and producing
a non-bootstrap self-hosted runtime provider are neither one-liners nor
this pass's scope, and the gate must not be weakened to accommodate their
absence. Settling requirements for #4-#6 are therefore:
1. provision `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
   matching sha256 `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`
   (decide whether it belongs in-repo or in a fetch step — its absence
   makes this gate unrunnable on any fresh checkout, which is a
   reproducibility hole in the campaign's most load-bearing gate);
2. produce a non-bootstrap self-hosted runtime provider `.so` and pass it
   with its attested sha;
3. then run the gate in a clean worktree (walls 1-5 are already known
   satisfiable) and capture `window_id` + PNG/PPM + the ~25 statuses.

**Revised scoreboard: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN** — no
cell moved to GREEN, but three moved from UNKNOWN to BLOCKED-with-a-named
cause and an actionable provisioning list, and the campaign now knows its
top gate cannot run on a fresh Linux checkout as shipped.

## Font-asset provisioning: the mechanism was "committed in-repo", and a chore commit removed it TODAY (2026-07-30)

**There is no fetch/submodule/setup mechanism to invoke, because none was
ever needed: the assets were tracked in git.** PROVED:

- `.gitmodules` declares 4 submodules, all under `examples/` (cuda,
  deeplearning, trace32, korean_stock) — **no font/assets submodule**.
- **Nothing** in `scripts/setup/` references `google-fonts`,
  `font_bundle`, or `assets/fonts`.
- `assets/fonts` is **not** gitignored — it was meant to be committed.
- `assets/fonts/**` has **3,787 commits of history**.
- `doc/03_plan/sys_test/simpleos_font_legal_bundle.md` and
  `scripts/os/simpleos_font_bundle_companion.sha256` (4,152 bytes, 35
  pinned companions: `METADATA.pb` + `OFL.txt` per family) are
  **consumption/verification** artifacts — they pin and stage bytes that
  are assumed already present. Neither fetches anything.

**Root cause of wall 7 (PROVED):** commit `a4b4c008aff`
*"chore: clean undeclared root artifacts"* — authored by the repo owner
(Yoon, `Yoons-MacBook-Air.local`) on **2026-07-30 14:05:23 +0900, today** —
is **271 deletions and 0 additions**. It deleted **58 files under
`assets/fonts`**, of which **51 are under
`assets/fonts/google-fonts`**, including **16 `.ttf` files**. It is the
**last commit in which the pinned `notosansmono` TTF existed**, and it is
an ancestor of the current tip. No font-related file was added anywhere
in that commit, so this was a pure removal, **not** a relocation to a
bundle.

This is the *"chore-labelled bulk commits hide semantic changes"* pattern
again: a 273-file cleanup carried a change that silently disabled a
verification surface.

**Why it was swept (INFERRED, high confidence):** the commit title says
"undeclared", and `CLAUDE.md` documents the FILE.md manifest policy
("Each directory can have a FILE.md declaring allowed entries", enforced
by `scripts/check-workspace-root-guard.shs`). There is **no
`assets/FILE.md`** and the root `FILE.md` does not mention `assets`, so
the tree was undeclared and a manifest-driven sweep would remove it. The
sweep was therefore *policy-correct* and the *gates* were relying on
undeclared content — two repo policies in direct conflict.

### Blast radius (PROVED)

**34 source consumers reference `google-fonts`** and are unrunnable-as-shipped
on a fresh checkout:

| Area | Count | Named |
|---|---|---|
| `scripts/check` gates | 5 | `check-linux-hosted-wm-live-window-evidence.shs`, `check-simpleos-wm-fullscreen-evidence.shs`, `check-rocm-engine2d-font-readback.shs`, `check-rv64-display-smoke-qmp-evidence.shs`, +1 under `check/lib` |
| `scripts/os` staging | 2 | incl. `make_os_disk.shs` (FAT32/initramfs staging) |
| `src` | 6 | font registry / readback harness paths |
| `test` specs | 21 | incl. `test/02_integration/os/port/simpleos_font_asset_staging_spec.spl` |

So this is not one blocked cell — it is **5 gates, 2 OS-image staging
owners and 21 specs**, i.e. the font-dependent verification surface
entirely, plus SimpleOS disk images that stage fonts.

### Verdict: STOPPING — this is a repo-policy decision, not an autonomous fix

Restoring is *mechanically* trivial (`git checkout a4b4c008aff^ --
assets/fonts/google-fonts`, no network, `curl`/`wget` not needed) but it
would **directly revert the repo owner's deliberate same-day commit**,
and it would restore content the FILE.md guard considers undeclared, so
the next sweep removes it again. Per brief, options with recommendation:

- **Option A (recommended): restore + declare.** Restore the 51
  google-fonts paths from `a4b4c008aff^` **and** add an `assets/FILE.md`
  (plus a root-manifest child link) declaring the tree, so the manifest
  guard stops classifying it as undeclared. Cheapest, no network, keeps
  gates runnable on a fresh clone, and resolves the policy conflict at
  its cause. Needs owner sign-off because it reverses today's commit.
- **Option B: keep the tree out of git; add a sanctioned provisioning
  step.** New `scripts/setup/` step that materializes the fonts and
  verifies them against the existing pinned sha256s. Keeps the repo free
  of vendored binaries (which the cleanup may have intended) but requires
  inventing a mechanism and a network source — explicitly out of scope
  for me to author unilaterally.
- **Option C: re-pin the gates onto a font that is in-repo.** Rejected:
  the pins are legal-provenance companions (OFL/METADATA) and re-pinning
  would weaken the licence-attestation the bundle exists to prove.

I did not implement any option, fabricate an asset, or weaken a gate.

### Wall 6 recorded as coupled to the seed-redeploy lane (INFERRED)

`runtime-provider-bootstrap-forbidden` fires because the only
self-hosted-lineage runtime `.so` on this host is the bootstrap one
(`src/compiler_rust/target/bootstrap/deps/libsimple_runtime.so`). A
deployed **non-bootstrap** self-hosted runtime provider would plausibly
satisfy it, so this wall may resolve itself when the sibling lane's seed
candidate lands. **Confirmation required:** after redeploy, re-run the
gate in a clean worktree passing the new provider via
`SIMPLE_WM_RUNTIME_LIB` + attested `SIMPLE_WM_RUNTIME_LIB_SHA256`, and
check that `runtime_provider_status=pass` — i.e. that the gate's
bootstrap-detection does not also reject the redeployed provider. Marked
INFERRED until that run exists.

**Scoreboard unchanged: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN** — but
wall 7's cause is now a known, dated, one-commit regression with a named
owner decision required, and the blast radius is 34 consumers rather than
3 cells.

## Option A implemented (2026-07-30) — wall 7 CLEARED; wall 6 is the sole remaining barrier

Owner approved Option A (restore + declare); landed as `cdadda01da2`.

**Restore (PROVED byte-exact).** A sibling lane had already restored the
`bungee` family (3 files — TTF + `METADATA.pb` + `OFL.txt`, verified
byte-exact against `a4b4c008aff^`), but had **not** restored the pinned
`notosansmono` asset, so wall 7 was still broken. The remaining **54**
paths were restored from `a4b4c008aff^` by git plumbing (`update-index
--cacheinfo` with the historical blob hashes, mode 100644) — no text-mode
round-trip. At origin: **57/57 font files present, 0 byte mismatches**
against `a4b4c008aff^`, and the pinned asset hashes to
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081` —
exactly the gate's `FONT_ASSET_SHA256`. Full bundle, not a subset: the 34
consumers reference all 16 `.ttf` families and the companion file pins 35
`METADATA.pb`/`OFL.txt` files, so a font is never restored without its
licence companion.

**Declare.** Added `assets/FILE.md` (declaring `fonts/`, `cldr/`,
`google-fonts/{CORPUS.sdn,apache/,ofl/}`, and recording why the tree is
tracked and what breaks if removed) plus both root `FILE.md` links (Root
Files row + Child Manifests row).

**Verification (a) — manifest guard:** `scripts/check-workspace-root-guard.shs`
passes (rc=0, zero assets findings) with the tree restored and declared.

**CORRECTION to this census's earlier INFERRED cause:** that guard does
**not** flag `assets/`. It returned rc=0 even with 57
tracked-but-undeclared asset files staged, *before* any declaration
existed. So the removal was a **manual/human "undeclared" judgement, not
a guard-driven sweep**, and the declaration is intent-documentation plus
defence-in-depth — it is *not* what unbreaks the guard. The earlier
high-confidence inference is withdrawn.

**Verification (b) — wall 7:** CLEARED, proven by equivalence rather than
observation: the gate's check is exactly
`sha256(FONT_ASSET) == FONT_ASSET_SHA256`, and the restored file's sha256
equals that constant. The gate no longer reaches wall 7 because **wall 6
fires first**.

### Wall 6 is now the SOLE remaining barrier for cells #4-#6

Re-run after the restore (clean worktree, `SIMPLE_BIN`=stage2 self-hosted,
provider passed with attested sha): the only `reason=` emitted is
`runtime-provider-bootstrap-forbidden`. Walls 1-5 satisfied, wall 7
satisfied. **The single thing between this campaign and its first three
GREEN cells on linux-x86_64 is a deployed non-bootstrap self-hosted
runtime provider** — which the sibling seed-redeploy lane has flipped to
GO. Settling command after redeploy:

```
SIMPLE_BIN=<redeployed self-hosted> \
SIMPLE_WM_RUNTIME_LIB=<non-bootstrap provider .so> \
SIMPLE_WM_RUNTIME_LIB_SHA256=<its sha256> \
sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs
```
run in a clean worktree; expect `runtime_provider_status=pass`, then the
~25 window/input/semantic assertions execute for the first time here.

**Scoreboard: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN** — unchanged in
count, but #4-#6 are now blocked on exactly ONE named, already-in-flight
prerequisite instead of two, and the 34-consumer font regression is fully
repaired at origin.

## Process hazard recorded: `FETCH_HEAD` is unsafe in the shared clone

While landing this, `git rev-parse FETCH_HEAD` in the shared working copy
returned `2cf72ec21f1` — the June-14 head of a Codex branch, i.e. the same
sha involved in an earlier mispush-to-main incident — because a concurrent
session's fetch had overwritten the shared `.git/FETCH_HEAD` between my
fetch and my read. Origin `main` was fine (`ls-remote` confirmed
`7a18961e303`, with the restore still an ancestor). **Use the sha from
`git ls-remote` as the base, never a re-read of `FETCH_HEAD`, when landing
from a shared clone.**

## Deployment pass (2026-07-30) — wall 6 CLEARED without deploying; NO deployment performed; deployed toolchain is NON-CANONICAL

### LOUD FINDING: the live compiler is a no-LLVM build (PROVED)

`scripts/check/check-compiler-provenance.shs` on the live
`bin/release/x86_64-unknown-linux-gnu/simple` (the target of the
`bin/simple` symlink) reports **`backends: llvm::=0 lld::=0`**, the
**"LLVM codegen linked" marker `absent`**, `lineage: HYBRID: 1 Simple
symbol + 15161 Rust-mangled`, size **57,345,808**, mtime **2026-07-29
06:00:33**, sha256 `40edbb4989132623…`.

Earlier in this same session the identical path reported
`backends: llvm::=51356`, marker **PRESENT**, size **145,448,208**,
sha256 `e5c461a5f0cba9ba…`. **The good LLVM binary was replaced by a
no-LLVM one.**

The two statements the coordinator flagged as "in tension" are in fact
consistent — there are **three** artifacts, not two:
`doc/09_report/seed_redeploy_readiness_2026-07-30.md` compares its
154,084,544-byte candidate against a *then*-deployed **145,448,208**-byte
LLVM binary (markers identical), and separately **warns** that "a plain
`cargo build --release` produces a NO-LLVM binary (57 MB, LLVM marker
absent) — not deploy-equivalent". The artifact live right now matches that
warning exactly. So the session has, since 2026-07-29 06:00, been
measuring against the non-canonical no-LLVM toolchain. Canonical recipe
per that report: `cargo build --profile bootstrap -p simple-driver
--features llvm`.

**Rollback/forensics preserved, nothing overwritten.** Both artifacts are
saved outside the repo at
`<scratchpad>/binforensics/simple.deployed-noLLVM-2026-07-29.bak` and
`<scratchpad>/binforensics/simple.goodLLVM-e5c461a5.bak`. The good LLVM
baseline still exists in-tree at `build/fable_s2/runtime/simple`
(145,448,208 / `e5c461a5f0cba9ba`, exact match). Only **one** deploy path
is live: `bin/release/x86_64-unknown-linux-gnu/` (with `bin/simple`
symlinked to it); `bin/release/linux-x86_64/simple` does **not** exist.

Restoring the canonical binary is a one-command shared-state change
(`cp build/fable_s2/runtime/simple <path>.new && mv <path>.new <path>`)
but it mutates the toolchain every parallel lane is using mid-flight, so
it is **not** done autonomously here — flagged for an explicit decision.

### No deployment was possible (PROVED)

- The GO candidate path `scratchpad/cargo_target_w/bootstrap/simple` is
  **ABSENT** (scratchpad swept); no 154,084,544-byte /
  `28e528ccd55d642d…` artifact survives anywhere on this host.
- Its own readiness report's headline is **"Recommendation: NO-GO — one
  blocking, candidate-only regression"**, so even if present it was not
  sanctioned for deployment.

### Wall 6 CLEARED — and it needed no deployment at all

The barrier was my own provider choice, not a missing build: I had only
ever passed the **bootstrap** runtime `.so`. Passing the **release**
provider instead —
`src/compiler_rust/target/release/libsimple_runtime.so` (9,368,952 bytes,
2026-07-30) with its attested sha256 — yields
**`runtime_provider_status=pass`**. The gate then ran for **40s** (versus
≤1s at every previous wall) and reached a genuinely new failure.

### NEW wall 8: `production-native-build-failed` — stale-binary, PROVED not a source defect

`build/linux-hosted-wm-live-window-evidence/native-build.log`:

```
Build failed: failed to parse .../src/os/hosted/hosted_browser_renderer_process.spl
at 970:13 during discovery: Unexpected token: expected identifier, found Dot
```

Line 970 col 13 is the `.` of `self.pid = browser_renderer_spawn_sandboxed(...)`
inside a `me begin_start(...)` method — i.e. the prefix-form receiver
whose synthesized name is `self`.

**Stale-binary, not a source bug (PROVED by differential parse):** the
Jul-29 deployed seed compiles that same file **past** the parse phase
(it fails later, in the *semantic* phase), while the Jul-28
`build/redeploy_out/simple_stage2` — the newest self-hosted-lineage
binary on this host, and the one the gate requires since it forbids the
seed — fails **at parse**. So the gate needs a *newer pure-Simple
self-hosted* binary.

**And none exists here:** every other self-hosted-lineage build is older
(`build/aggfix/*`, `build/coverage-bootstrap-586*/stage3`: 2026-07-27),
so stage2 (2026-07-28 00:11) is the newest available and it is already
too old. Wall 8 therefore resolves **only** via the bootstrap/redeploy
lane producing a fresh self-hosted binary — the same lane whose candidate
is currently NO-GO and missing. Not chased or worked around here, and the
gate was not weakened.

### Cells #4-#6 status

**BLOCKED** — still, but the barrier moved and is now one lane away:
walls 1-5 pass, **wall 6 passes**, wall 7 passes, and wall 8 is a stale
self-hosted binary. Settling sequence:
1. bootstrap/redeploy lane produces a fresh pure-Simple self-hosted
   binary (canonical recipe above) that parses `self.field = …` in `me`
   methods;
2. re-run the gate in a clean worktree with `SIMPLE_BIN=<that binary>`,
   `SIMPLE_WM_RUNTIME_LIB=src/compiler_rust/target/release/libsimple_runtime.so`
   plus its attested sha256;
3. expect the native-build to complete and the ~25 window/input/semantic
   assertions to execute for the first time on this host.

**Scoreboard: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN** — unchanged in
count. Wall 6 is retired; the live-toolchain finding above is the pass's
most consequential result.

## Toolchain provenance, settled with the script's own marker method (2026-07-30, follow-up)

Re-checked using exactly `check-compiler-provenance.shs`'s method —
`strings -a <bin> | grep -cF <literal>` over its four MARKER literals — so
all three artifacts are apples-to-apples. **This changes the
recommendation: the `bootstrap-clobber-bak` is evidence of the regression
but is NOT a restore candidate.**

| Artifact | Date | Size | `[jit-fallback]` | `SIMPLE_JIT_STRICT` | `rt_index_of` (`.?` fix) | `ambiguous LLVM method resolution` |
|---|---|---|---|---|---|---|
| **live** `bin/release/x86_64-unknown-linux-gnu/simple` (`40edbb49`) | 2026-07-29 06:00 | 57,345,808 | 1 | 2 | **9** | **0** |
| `simple.bootstrap-clobber-bak` (`ce2fcaff`) | 2026-07-23 03:41 | 124,596,016 | **0** | **0** | **0** | **1** |
| `build/fable_s2/runtime/simple` (`e5c461a5`) | 2026-07-28 12:13 | 145,448,208 | 1 | 2 | 4 | **1** |

Readings:

- **The dated toolchain regression is CONFIRMED** on the LLVM axis: the
  live binary carries **no** LLVM codegen marker (and 0 `llvm::` strings,
  vs 576 in the clobber-bak), so everything measured since 2026-07-29
  06:00 ran on a no-LLVM, non-canonical toolchain.
- **But the clobber-bak is strictly OLDER in capability**: it has **none**
  of the three fix markers (JIT manifest, strict-mode knob, `.?` fix) —
  it predates them. Restoring it would trade LLVM for the loss of three
  landed fixes. It is diagnostic evidence, not a rollback target.
- **`build/fable_s2/runtime/simple` (`e5c461a5`) is the only artifact with
  LLVM *and* all three fixes** — the correct restore target, and the
  binary this session began against.

### Why the restore is still NOT performed autonomously (sharpened)

Beyond the shared-state risk, there is now positive evidence the live
binary is **newer on at least one axis**: `rt_index_of` occurs **9** times
in the live binary versus **4** in the `e5c461a5` baseline. The
provenance script only tests presence (`>0`), so this count delta is not
proof of extra behaviour — but it is consistent with the live binary
containing later `.?`/`rt_index_of` work that the baseline lacks.
Restoring the baseline could therefore **silently revert another lane's
landed fix**, which is exactly the failure mode the anti-revert rule
exists to prevent. Settling that question requires identifying which
commit produced the live 57MB binary (INFERRED: a plain
`cargo build --release`, per the readiness report's warning) and diffing
its `.?`-related content against `e5c461a5` — not a judgement to make by
overwriting first.

Recommended sequence for whoever owns the toolchain:
1. Rebuild canonically — `cargo build --profile bootstrap -p simple-driver
   --features llvm` — which yields LLVM **and** current source, making the
   restore-vs-newer dilemma moot;
2. verify all four markers PRESENT plus `llvm::` >> 0 with `lld::` = 0;
3. `.new` + `mv` into `bin/release/x86_64-unknown-linux-gnu/` (the only
   live deploy path; `bin/release/linux-x86_64/` does not exist);
4. keep `simple.deployed-noLLVM-2026-07-29.bak` as the rollback.

### Deployment: still not possible (re-confirmed)

`scratchpad/cargo_target_w/bootstrap/simple` is **STILL ABSENT** on
re-check, and no `28e528ccd55d642d` / 154,084,544-byte artifact exists
anywhere on this host. Its readiness report's headline remains
**"Recommendation: NO-GO"**. So steps 2-4 of the deployment brief have no
sanctioned artifact to act on; nothing was deployed, nothing overwritten,
and no `.new` file was left behind.

**Scoreboard unchanged: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN.** The
host-WM cells remain blocked at wall 8 (stale self-hosted binary), which
the same canonical rebuild would also address.

## Deployment DONE + wall 8 resolved into a real parser defect (2026-07-30)

### Deployment record

| Field | Value |
|---|---|
| Deployed | `bin/release/x86_64-unknown-linux-gnu/simple` (the only live deploy path; `bin/release/linux-x86_64/` does not exist) |
| Artifact | 154,094,616 bytes, sha256 `79ca755dd8e7dabf989f800b…`, built 2026-07-30 07:35 |
| Source commit | `d05afd1276` (per the seed lane), i.e. fresher than the binary it replaced |
| Method | forensic copy, then `.new` + `mv` (never `cp` over a running binary) |
| Rollback | `bin/release/x86_64-unknown-linux-gnu/simple.deployed-noLLVM-2026-07-29.bak` (57,345,808 bytes, sha256 `40edbb49…`) |
| Post-deploy provenance | all four markers PRESENT (`[jit-fallback]`=1, `SIMPLE_JIT_STRICT`=3, `rt_index_of`=5, LLVM=1); `backends: llvm::=57617 lld::=0`; smoke run exits 0 |

**LLVM-regression verdict on the old binary, stated plainly: the binary
live on this host from 2026-07-29 06:00 until 2026-07-30 09:08 had ZERO
`llvm::` strings and no LLVM-codegen marker, versus 617/present in the
replacement. Every measurement taken on this host in that window ran on a
non-canonical, no-LLVM toolchain.**

Scope caveat, stated so the record is not overclaimed: **the deployed
binary is still a Rust bootstrap seed** (`lineage: HYBRID`, and its own
version banner says "bootstrap seed only"). The prior binary was also a
seed, so this deploy did **not** introduce a seed-vs-pure-Simple
regression — it restored LLVM codegen within the same class. This host
does **not** now run the pure-Simple tool.

### Consequence for the host-WM gate: the deploy does not help it

The gate **forbids the seed** (wall 3, `rust-seed-forbidden`), so the
newly deployed binary cannot be its `SIMPLE_BIN` — re-confirmed by
running it: `reason=rust-seed-forbidden` in 0s. The gate still needs a
*pure-Simple self-hosted* binary, and the newest one on this host remains
`build/redeploy_out/simple_stage2` (2026-07-28).

### Wall 8 RE-CHARACTERIZED: not stale-binary any more — a real parser defect

Re-run with stage2 + the release runtime provider: walls 1-7 pass
(`source_provenance_status=pass`, `runtime_provider_status=pass`), the
gate runs 26s and fails at `production-native-build-failed`. The failing
file **moved** (origin advanced ~10 commits since my previous run):

```
failed to parse .../src/lib/common/web/browser_renderer_protocol.spl
at 559:38 during discovery: Unexpected token: expected expression, found Newline
```

**The newly deployed, newest, LLVM-linked seed fails on the same file
with the same error** — so unlike the previous wall-8 instance
(`hosted_browser_renderer_process.spl`, which was genuinely stale-binary),
this one is **NOT** a binary-age problem. It is a grammar/source
incompatibility live at origin tip.

Minimal repro (PROVED): operator line-continuation is accepted in a
binding but rejected in an `if` condition —

```simple
val x = a +
   b          # PARSES

if a >
   b:         # FAILS: expected expression, found Newline
```

Introduced by `ba0ce4e3c06` *"feat(web): add SBR2 command capability
codec"* (2026-07-30). Filed as
`doc/08_tracking/bug/if_condition_operator_line_continuation_parse_2026-07-30.md`
with both fix options; **not** chased here and the gate was **not**
weakened. Per CLAUDE.md the one-line workaround is deliberately not
applied unilaterally, because it would encode the grammar inconsistency
rather than fix it.

### Cells #4-#6

**BLOCKED** (not GREEN). Walls 1-7 pass; the sole barrier is now the
parse defect above, which blocks the gate's production native-build. It
is a one-file, two-line source form with an identified introducing commit
— materially smaller than every previous barrier, and it blocks any lane
that compiles `browser_renderer_protocol.spl`, not just this gate.

**Scoreboard: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN.**

## Canonical deploy + parser fix verified; wall 8 traced to a THIRD parser surface (2026-07-30)

### Deployment record #2 (canonical recipe)

| Field | Value |
|---|---|
| Recipe | `cargo build --profile bootstrap -p simple-driver --features llvm` (6 min) |
| Artifact | 154,095,344 B, sha256 `ea4af9a4498297e3…`, built from tip `9ea0b39962d` (contains parser fix `023a60a05aa`) |
| Pre-deploy gates | all 4 markers PRESENT (2/5/5/1); `llvm::`=617, `lld::`=0; size in the ~154 MB band; `--version` sane; **parser fix confirmed present before deploying** |
| Deployed to | `bin/release/x86_64-unknown-linux-gnu/simple` via `.new` + `mv` |
| Rollback | `simple.pre-parserfix-79ca755d-2026-07-30.bak` (154,094,616 B) |
| Post-deploy provenance | `backends: llvm::=57617 lld::=0`, all 4 markers PRESENT |

LLVM remains restored; this deploy swapped one LLVM build for a newer
LLVM build that additionally carries the parser fix.

### The parser fix WORKS — PROVED end-to-end

Running the gate's exact `native-build` command with the newly deployed
seed:

- **before:** failed in ~1 s with
  `failed to parse …/browser_renderer_protocol.spl at 559:38 during
  discovery: Unexpected token: expected expression, found Newline`;
- **after:** **zero** occurrences of that error and zero `during
  discovery` failures — it progressed past discovery into real
  compilation and was still compiling at the 10-minute mark.

So wall 8's source cause is genuinely fixed.

### But the GATE is still blocked — by a THIRD parser surface (PROVED)

The gate must pass a **non-seed** `SIMPLE_BIN` (wall 3), so it runs
`build/redeploy_out/simple_stage2`. Reproducing the gate's exact
`native-build --source … --entry …` invocation *outside* the gate:

| Binary running native-build | Discovery result |
|---|---|
| deployed seed (fixed, today) | **passes discovery** |
| `simple_stage2` (2026-07-28) | **still fails** at 559:38 |

And stage2's *other* path disagrees with its own build path:
`stage2 compile --format=smf` **accepts** the continuation (both the
minimal repro and the real file), while `stage2 native-build` **rejects**
it. The error text comes from
`src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs:904`
— i.e. **Rust** code — so `simple_stage2` is a hybrid that embeds its own
copy of the Rust pipeline, compiled 2026-07-28, with the pre-fix parser.
My fix cannot reach it: it is baked into that binary.

**Consequence:** wall 8 for the gate is no longer a source defect (fixed)
nor the deployed toolchain (fixed) — it is **stale embedded Rust code
inside `simple_stage2`**. Clearing it requires a fresh self-hosted /
stage2 build produced from current source, which the bootstrap-redeploy
lane owns. That rebuild is now *unblocked* by the parser fix: the seed can
finally parse the offending file, which it could not do this morning.

### Also confirmed: the `--source` widening hazard is real

The gate's `native-build --source "$ENTRY"` with `SIMPLE_LIB=src` emits
`[memory-guard] SIMPLE_LIB=src contains 600+ .spl files — consider
narrowing scope`, and the run exceeded **10 minutes** without finishing.
So even once stage2 is rebuilt, this gate's build step is a ~10 min+
operation, not a quick check — budget accordingly.

### Cells #4-#6

**BLOCKED**, unchanged in status but with the barrier reduced again and
now owned elsewhere: walls 1-7 pass, wall 8's source and toolchain causes
are both fixed, and the only remaining blocker is a stale `simple_stage2`.

Two claims kept separate, as required: this host now runs a **canonical
LLVM-linked seed**, which is *not* the same as running the pure-Simple
tool. The deployed binary still self-identifies as a bootstrap seed, and
the gate still rejects seeds; a pure-Simple self-hosted `SIMPLE_BIN` is a
separate open problem.

**Scoreboard: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN.**

## Cell #1 `widget × headless (interpreted)` verified GREEN (2026-07-30)

Full evidence: `doc/09_report/showcase_cell_widget_headless_green_2026-07-30.md`.

Pass criteria were declared **before** the first run, because this cell's
claim is more diffuse than cell #2's single checksum. All matched exactly,
first properly-configured attempt:

| Criterion | Claimed | Observed |
|---|---|---|
| 640×480 P6 PPM artifact | `P6 640 480 255` | `P6 640 480 255` |
| nonzero pixels | 921,600 / 921,600 | 921,600 / 921,600 |
| distinct byte values | 74 | 74 |
| widget types | 24 | 24 |
| font cold / warm-hits | 10 / 20 | 10 / 20 |
| 320×240 repeat, distinct bytes | 64 | 64 |

`showcase_font_loaded=true`, font identity equals the expected identity
(`sha256=c4f5361c…;axes=static`), software offscreen lane, entry
`examples/06_io/ui/widget_showcase_gui.spl` (the true `examples/` path).
Binary: canonical `ea4af9a4498297e3…` (154,095,344 B, 4/4 markers,
`llvm::`=617). Source commit `a7a5bb3c0f2`. 95 s at 640×480, 46 s at
320×240. PPM payload sha256 `9c6b02ff035fcaa23c6956a4…`.

Two notes for whoever re-runs it:
- `SHOWCASE_PPM` is **required** to get an artifact at all — without it the
  run ends "No GUI requested … headless only." and writes no file, so the
  nonzero/distinct criteria cannot be evaluated (the other three are still
  visible in the trace).
- The claim's "921,600 nonzero px" counts **RGB bytes**; the program prints
  `rendered 307200 px`, and 307,200 × 3 = 921,600. Consistent, not a
  discrepancy — worth stating so nobody reads it as a mismatch.

The font-tree trap from cell #2 was avoided by construction: the run used a
worktree at the target commit with `find assets/fonts -type f | wc -l` = 57
verified beforehand, never the shared working copy (whose HEAD predates the
restore `cdadda01da2` and which has `core.sparseCheckout=true`, so
`assets/fonts` is empty under a completely clean `git status`).

**Scoreboard: 2 GREEN, 0 CLAIMED, 5 BLOCKED, 0 UNKNOWN.**

Both headless cells are now verified on linux-x86_64 with today's canonical
binary: `2D × headless` (landed `3b3fe52cbb7`) and `widget × headless`
(this pass). No cell remains in CLAIMED — every remaining cell is BLOCKED
with a named cause, and the campaign's top line is, for the first time,
backed by artifacts produced on this host rather than by inherited reports.

## Co-import defect RESOLVED — but the three host-WM cells stay BLOCKED (2026-07-30)

Re-tested the blocker that the matrix records against all three host-WM
rows (`doc/08_tracking/bug/co_import_makes_module_unresolvable_wm_contract_gui_renderer_2026-07-27.md`).
**It no longer reproduces.** Bug doc updated to RESOLVED with the full
re-test; original report preserved.

Four checks, all clean on the canonical binary (`ea4af9a4498297e3…`):
both namespace spellings (`common.ui.…` and `std.common.ui.…`) resolve;
the symbols are **used, not merely imported**, so nothing can be pruned;
and both `run` and `compile` are free of `Cannot resolve module`.

The report's load-bearing claim is now false: **`GuiRenderer.create` IS
reached.** It executes its engine dispatch and returns `nil` for a reason it
prints itself — it is no longer dying in the semantic phase.

**What stops a window today is different and smaller:** with a valid engine
under Xvfb, `create` fails at
`cannot load build/sffi/libspl_winit.<dylib|so|dll> — build it first`. That
is an unstaged build artifact (the library exists at
`src/runtime/spl_winit/target/release/libspl_winit.so`, 2026-07-25, just not
at the default candidate path), not a semantic defect — and the evidence
gate does not even hit it, because it builds `spl_winit` itself and passes
`SIMPLE_WM_WINIT_LIB` explicitly.

### The two barriers remain independent — cells are NOT nearly-green

| Barrier | State |
|---|---|
| co-import semantic defect | **RESOLVED** (this pass) |
| stale `simple_stage2` (embedded Rust from 2026-07-28 rejecting the operator line-continuation my parser fix repaired) | **OPEN**, owned by the bootstrap/redeploy lane |

Clearing the first does **not** clear the second. Cells #4-#6 remain
**BLOCKED** on the stale-stage2 problem alone; they should not be reported
as close to GREEN on the strength of this result.

**Scoreboard unchanged: 2 GREEN, 0 CLAIMED, 5 BLOCKED, 0 UNKNOWN.**

## Pointer (2026-07-31): cell 3's `SHOWCASE_DIMS`/module-init framing is fixed and deployment-gapped, not a new gap

A later re-audit re-confirmed `doc/08_tracking/bug/
jit_run_file_pipeline_gaps_2026-07-30.md` §16-§17: the module-level-`val`
write-side defect this table's cell-3 row does not itself name (the
`text.from_any`/paint-budget framing above is a separate, earlier-dated
finding) is fixed at `48af531ce0e`, confirmed an ancestor of origin/main
tip `cba4abb304c3735861c5ebfac2af9a41d7e9c3ca` via `git merge-base
--is-ancestor` (not dates). The **deployed** canonical binary
(`ea4af9a4498297e3…`, same sha this report already cites) still predates
that fix, so a plain `bin/simple run` of the showcase still prints
`pixels=0` today — a redeploy gap, not an unfixed source defect. Cell 3's
real current blocker, once run on a post-fix binary, is the
font-identity/Draw-IR pairing defect at §16.6 (still open, not the
module-init one). See §17 there for the full binary-by-binary evidence
table.

## Cell #7 `SimpleOS-WM × QEMU` re-tested, still BLOCKED — but the recorded blocker is stale (2026-07-31)

This entry's recorded blocker was the missing-vtable `ud2` trap. A triage
pass found its source-side fix, `f2f64a137bd9518c06ea33236ecc16504a73830a`
(2026-07-28), with no dated post-fix QEMU re-run. Verified by
`git merge-base --is-ancestor f2f64a137bd9518c06ea33236ecc16504a73830a
465ec1cd334` (exit 0, PROVED, not inferred from commit dates): the fix **is**
in origin `main` (confirmed against tip `465ec1cd34345fd7be512289c14ebccc3918ffe0`,
still an ancestor of the current tip).

A fresh re-run in a detached worktree at that tip (existing pure-Simple
`stage3` binary, sha256 `c0d1ed629b18f…`; no cargo build; 57 files present
under `assets/fonts`, so the shared-WC sparse-checkout trap does not apply)
via `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` produced
`status=fail reason=wm-simple-web-build-failed`. This is **neither** of the
two previously recorded outcomes: the kernel link now fails *before* QEMU
ever starts (`serial_log_bytes=0`), on a gate that did not exist when the
vtable trap was last observed. `config/freestanding_fabricated_stub_baseline.sdn`
(the fabricated-stub ratchet, armed 2026-07-29 — one day **after** the
vtable fix) now reports 120 known/baselined fabricated symbols plus **4 new,
unbaselined** ones for `simpleos_wm_production_desktop.elf.candidate`:
`rt_cuda_device_identity`, `rt_raw_i64_to_string`, `rt_string_byte_at`,
`rt_vulkan_accepted_compute_submit_count`. The ratchet correctly refuses to
silently link nil-returning stubs for them (that exact failure mode
previously shredded every array copy in a guest, per the ratchet's own
commit message) — not weakened here.

Full details, reproduction, and per-symbol notes:
`doc/08_tracking/bug/simpleos_wm_freestanding_new_fabricated_symbols_2026-07-31.md`.
Report: `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-31.md`.

**Net effect on the census: cell #7 stays BLOCKED.** But the *reason*
recorded for it was stale and is now corrected: the vtable trap is
confirmed fixed in `main`; neither it nor the font-metrics hang could be
re-tested this pass because a newer, earlier-stage regression (4 newly
unbaselined freestanding symbols) now blocks the kernel link first. The
next SimpleOS-WM attempt should start from the bug doc above, not from the
vtable trap.
