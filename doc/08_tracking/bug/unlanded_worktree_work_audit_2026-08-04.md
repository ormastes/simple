# Unlanded worktree work audit (2026-08-04)

Read-only audit of the 207 inventoried worktrees, focused on the 93 whose HEAD is
not an ancestor of `origin/main`, plus the 57 dirty and 34 no-`.git` directories.
**Nothing was landed except this document.** No worktree was modified, deleted, or
checked out.

- Base used: `origin/main` = `85a51c4adeb076cafe74b265a19e6a8ffe0a75e2`
  (re-fetched over SSH; the inventory's `c019b5bf724` is an ancestor of it).
- All 93 non-ancestor HEAD objects resolved (`git cat-file -t` = `commit`).
  **Zero "GONE" verdicts** — no missing-object false negatives.
- Every git call isolated with `env -u GIT_DIR`; `/usr/bin/grep` pinned.

## Method — why sha comparison was not used

134 of the 250 distinct commit subjects across the 93 worktrees are **already in
`origin/main`'s history under a different sha** (rebased/cherry-picked). Subject
and sha are therefore both useless as evidence. Classification is by *content*:

For each worktree, with `MB = merge-base(origin/main, HEAD)`:

1. `OWN` = files changed by `MB..HEAD` — what this worktree actually touched.
2. `UNIQUE` = the subset where `blob(HEAD:f) != blob(origin/main:f)`.
3. `CLEAN` = the subset of `UNIQUE` where `blob(MB:f) == blob(origin/main:f)`
   — i.e. **origin never touched that file since the fork point**, so the
   worktree's version is genuinely unlanded rather than superseded.
4. `CONTESTED` = `UNIQUE - CLEAN` — origin moved the same file independently;
   ambiguous, may be a re-implementation.

Symbol-level confirmation (`git grep "fn <name>" origin/main -- src/`) was used
for every claim that something exists *nowhere* at origin.

## Counts

| Class | Count | Basis |
|---|---|---|
| (i) superseded — zero unique files vs origin | 10 | every file the worktree touched is byte-identical to origin |
| (i-probable) contested-only — unique files, but origin independently moved all of them | 45 | re-implemented or rebase residue; no clean unlanded delta |
| (iii) worktrees holding genuinely unlanded content | 38 | at least one `CLEAN` file |
| dirty worktrees examined | 57 | `git status --porcelain` |
| no-`.git` plain copies examined | 34 | filesystem diff vs origin tree |

The 38 collapse into **10 distinct bodies of work** — several lanes keep 2–6
rebased clones of the same chain.

---

# PROMINENT: intact module versions for the truncation-restore lane

Two modules that `doc/08_tracking/bug/tree_wipe_module_damage_census_2026-08-04.md`
flags as damaged have **larger copies on disk that define symbols existing nowhere
at `origin/main`**. A working copy beats a reconstruction — hand these to the
restore lane rather than re-growing the API.

### 1. `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl`
- Census row 10: 1450/2073 lines, 11% damage.
- Origin: 52,564 bytes, **105 `fn`**. Intact copy: **76,365 bytes, 148 `fn`**.
- **51 functions present only in the copy; 8 present only at origin** (so it is a
  merge, not a straight revert — do not blind-overwrite).
- Verified absent from all of origin `src/`: `be_dom_apply_default_action_to_id`,
  `be_dom_checked_radio_id_for_target`.
- **Path:** `/home/ormastes/dev/pub/simple-dom-identity-lane2-wt/src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl`

### 2. `src/os/compositor/shared_mdi_framebuffer_scene.spl`
- Census row 6: 241/514 lines, 46% damage.
- Origin: 9,997 bytes, **10 `fn`**. Intact copy: **14,397 bytes, 21 `fn`**.
- 14 functions only in the copy, 3 only at origin. Verified absent from all of
  origin `src/`: `render_shared_mdi_framebuffer_scene_for_windows`,
  `shared_mdi_lifecycle_seed_windows`, `render_shared_mdi_app_content`.
- **Paths (7 byte-identical copies):** `/home/ormastes/dev/pub/simple-fw-prod`,
  `simple-fs-wave`, `simple-fw-doc`, `simple-fw-pt-20260707`,
  `simple-llm-caret-env-validation`, `simple-simd-cross-proof`,
  `simple-wal-meta-sync` — all under `src/os/compositor/`.

### Ruled out — do NOT restore these
- `src/os/compositor/host_compositor_entry.spl` (294 B at origin) is a
  **deliberate facade**, not a truncation: `host_compositor_core.spl` holds the
  123,425-byte body at origin. The 59,188-byte worktree copies are the *pre-split*
  monolith. The census already notes this; restoring it would undo a refactor.
- `src/os/compositor/wm_action_applier.spl`: the 25 "missing" functions in the
  larger copy **do exist at origin in other files**. Moved, not lost.
- 31 census paths (`src/compiler/core/parser.spl`, `src/compiler/backend/*`, …)
  do not exist at origin at all — they are pre-restructure path references in the
  census prose, not damage.

---

# Class (iii) — valuable unlanded work, ranked

Ranked by (unrecoverability x blast radius). **None of this was pushed.**

## 1. AOP / aspect-facet subsystem — largest and most fragile

- **Path:** `/home/ormastes/dev/pub/simple-aspect-facet` (**no `.git` — a plain
  directory**), plus **194 `(aop)` commits** in the shared object store, newest
  `314d11a4f4d` `docs(aop): reconcile MIR unwind groundwork` (2026-08-04 14:15Z).
- **Not one of the 194 is an ancestor of `origin/main`.** Zero of
  `aspect_catalog`, `aspect_activation`, `advice_binding_registry`,
  `aspect_facet_compiler_abi` appear anywhere in origin `src/`.
- **Scope:** 93 files matching `aspect*`/`advice*` — 30 source modules
  (~276 KB; `src/app/startup/aspect_application_runtime.spl` alone is 36 KB)
  spanning `src/app/startup`, `src/compiler/99.loader`, and four `src/lib` tiers,
  plus **37 specs** under `test/01_unit`, `test/03_system`, `test/unit`.
- **Applies cleanly:** YES — `git merge-tree --write-tree` of `314d11a4f4d` onto
  `origin/main` produces **no conflicts**.
- **Hazard:** commit `a44fd642416` `refactor(aop): add lazy activation transition
  leaves` is a **jj conflict commit** — its tree contains only
  `.jjconflict-side-0/…` paths. If that sha is ever pushed it wipes the tree.
  `scripts/check/check-no-conflict-tree-push.shs` must gate any landing of this
  chain, and the landing sha must be a non-conflicted descendant.
- **Why top-ranked:** the working directory has no `.git`; a `rm -rf` of that one
  path destroys the only checked-out copy. The commits survive only as long as
  the shared object store is not gc'd.

## 2. LLVM 23.1 signed-provider + Stage-4 x86 phase-4 bootstrap chain

- **Best tip:** `/home/ormastes/dev/pub/simple-stage4-x86-phase4-llvm23-integrated`
  @ `1b6dde42a6ed0160da22ec148af7d657ebb97d20` (2026-08-04 13:41Z), **83 commits
  ahead**, 190 clean / 91 contested files, **98 files origin does not have**.
- Five sibling clones hold rebased variants of the same 83-commit chain, none an
  ancestor of another: `/tmp/simple-bootstrap-sdk-capsule-ac12` (`fb5059b`),
  `/tmp/simpleos-llvm23-gpg` (`d7c168a`), `/tmp/simpleos-llvm23-attestation`
  (`87d4557`), `/tmp/simple-freebsd-llvm23-provider` (`30b35a6`),
  `/tmp/simple-bootstrap-sdk-capsule-plan` (`0c79bef`). Land the integrated tip;
  the others are strictly older snapshots of it.
- **What it does:** introduces a signed LLVM 23.1 toolchain provider —
  `scripts/setup/build-llvm-23-1-provider.shs`,
  `scripts/setup/keys/llvm-release-tobias-hieta.asc` (GPG release key),
  `scripts/check/lib/llvm-23-1-signed-provider.shs`,
  `scripts/check/lib/clang-23-1-toolchain.shs`, and four contract gates
  (`check-llvm-23-1-provider-builder-contract.shs`,
  `check-freebsd-llvm-23-1-provider-contract.shs`,
  `check-simpleos-arm64-llvm23-provider-contract.shs`,
  `check-rust-bootstrap-llvm-isolation.shs`); plus ~20 new
  `test/03_system/native/stage4_*_contract.spl` Stage-4 ownership contracts, and
  edits to `src/compiler/70.backend/backend/llvm_{capability,target,version}.spl`,
  `src/compiler/90.tools/{lint,fix,formatter,leak_check,duplicate_check}`,
  `src/lib/nogc_sync_mut/{ffi,sffi}/llvm_loader.spl`, `src/os/port/llvm/*`.
  It also **adds `src/lib/json.spl`** (a json compatibility facade origin lacks).
- **Applies cleanly:** NO. Merge onto current `origin/main` conflicts in
  `doc/00_llm_process/llm_wiki.md`, `doc/08_tracking/bug/bug_db.sdn`,
  `doc/03_plan/design/bootstrap_sdk_capsule.md`, `.codex/skills/sp_dev/SKILL.md`
  and two more docs — all **generated/tracking files**, no source conflicts seen.
- **Value:** supply-chain security (GPG-verified toolchain provider) + the
  bootstrap path. Rewritable but expensive; 83 commits of work.
- **Specs:** not run — 83 commits over a live lane at ~32 host load; running the
  Stage-4 contract suite here would have been an hour of build. **Undetermined.**

## 3. ARM64 attested LLVM23 provider

- `/tmp/simple-arm64-attested-aa070-refresh` @ `ded982d787f0` (13:24Z, 134 clean /
  13 contested, 39 added) supersedes `/tmp/simple-arm64-attested-aa070-snapshot`
  @ `fcf78fcee8d5` (13:11Z).
- Touches `src/compiler` (25 files), `src/os`, `src/lib`, `scripts/check`,
  `test/01_unit`, `test/03_system`.
- **Applies cleanly:** NO — real source conflict in
  `src/compiler/20.hir/hir_types.spl` (plus auto-mergeable
  `hir_lowering/_Items/module_lowering.spl`). Needs a human merge.

## 4. engine2d draw-IR effect validation (the flagged item — see assessment below)

- **Module:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_effect_validation.spl`,
  12,816 bytes, **untracked** in 4 worktrees:
  `/home/ormastes/dev/pub/simple/build/worktrees/simpleos-engine2d-stage4-snapshot`,
  `/home/ormastes/dev/pub/simple-x25519-recovery`,
  `/tmp/simple-2d-current-stage4.jYckMj/worktree`,
  `/tmp/simple-x25519-stage4-stable-20260803.iKIW0Z/repo`.
- **Specs (also untracked, same dirs):**
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_effects_spec.spl` (16,243 B),
  `draw_ir_command_validation_spec.spl`, `draw_ir_gradient_plan_spec.spl`,
  `backend_emu_blur_rolling_spec.spl`.
- **Only git backing:** three *jj working-copy snapshot commits* with **empty
  descriptions** — `1c74085cfce`, `25c1e3c9015`, `de69bed23a7` (2026-08-04
  11:24–11:36Z), none an ancestor of `origin/main`. There is no described commit.
- Confirmed: `git grep -lE 'blur-rect|mask-rect|blend-rect'` on `origin/main`
  returns **0 files**. The hyphenated draw-effect vocabulary is genuinely absent.
  (An underscore form `blur_rect` does exist in the engine2d backends — do not
  mistake one for the other.)

## 5. `simple_l7_wt` — uncommitted engine2d backend hook

- `/home/ormastes/dev/pub/simple_l7_wt`, **uncommitted**: 18 files, +104/-0.
- Uniform small addition to every `src/lib/gc_async_mut/gpu/engine2d/backend_*.spl`
  (baremetal, cpu, cuda, directx, intel, metal, opencl, opengl, qualcomm, rocm,
  software, virtio_gpu, vulkan, webgpu), `backend.spl`, `draw_ir_adv.spl`,
  `engine.spl`, and `src/lib/nogc_async_mut/gpu/engine2d/backend.spl`.
- Purely additive and small — cheap to lose, cheap to redo, but it is a complete
  cross-backend sweep and redoing it means re-deriving all 18 call sites.

## 6. backend artifact-contract pair

- `/tmp/simple-backend-artifact-contract-20260803` and
  `/tmp/simple-backend-contract-integrate-20260803` — identical 11-clean-file
  deltas over 6 `src/compiler` files, 2 `src/app`, 2 `test/01_unit`, 1 guide.

## 7. `simple-2d-harden-recovery`

- `/home/ormastes/dev/pub/simple-2d-harden-recovery` @ `8e433a09ef27`, 26 clean
  files: 5 `src/compiler`, 4 `scripts/check`, tests, guides, an
  `examples/09_embedded` entry. Recent mtime.

## 8. `simple-bootstrap-adhoc-local`

- 17 clean files, all additive, 0 contested: 4 `src/app`, test fixtures,
  `doc/02_requirements`. Small and self-contained.

## 9. `simple-gpu-mmu-interface-wt` — uncommitted interpreter-extern split (LIVE)

- HEAD `3faa7531282` `fix(bootstrap): thread llvm scalar emission state`
  (2026-08-04 11:24Z). Working copy: **220 A / 1299 D / 1343 M / 3 R**.
- The 220 adds are a decomposition of `src/app/interpreter/extern/*`
  (`collections`, `conversion`, `coverage`, `diagram`, `file_io/{ffi_file,ffi_fs,
  ffi_term,file,fs,term}`, …).
- **The 1299 deletions make this dangerous**: an uncommitted WC this far behind
  origin, committed wholesale, is exactly the `chore(sync)` rewind pattern this
  repo has been bitten by. Class (iii) for the adds; the deletions must not ride
  along.

## 10. `simple-evidence-verify` / `simple-evidence-release`

- `a30ad65f6b1c` (2026-07-31) and `9999cb28e204` (2026-07-30) — 120 and 86 clean
  files, 57 and 55 additions, across `src/app`, `src/lib`, `doc/06_spec`,
  `test/03_system`, `.claude/skills`.
- **Five days stale and conflicting** on `.claude/agents/spipe/dev.md`,
  `.agents/skills/impl/SKILL.md`, `.claude/templates/spipe_template.spl`,
  three `.gemini/commands/*.toml`. Much of the release/evidence lane has landed
  since under other shas. Lowest confidence of the class-(iii) set — kept here
  only under the "when unsure, class (iii)" rule.

Also class (iii) but minor: the three `/tmp/simple-release-beta-{rebase,rebase2,
pr-v2}` clones (29–32 clean files, 20 A / 2 D each — near-duplicates of one
another), `simple-modres-old` / `simple-modres-wt` (probe `.spl` scratch at repo
root: `v_theme.spl`, `y_winit.spl`, `only_gui.spl` — arguably class (ii)), and
`/tmp/simple-backend-env-coverage-codex-20260803a` (5 files, 0 contested).

---

# Assessment: `engine2d_draw_ir_effect_validation`

**Finished work, not a work-in-progress** — but with one real caveat.

Evidence for finished:
- **Zero** `TODO`/`FIXME`/`unimplemented` markers in the 12,816-byte module.
- Complete, coherent API surface: 5 tuned budget constants
  (`ENGINE2D_DRAW_IR_MAX_EFFECT_PIXELS` 16 Mpx,
  `MAX_EFFECT_SURFACE_PIXELS` 33,177,600, `MAX_BLUR_RADIUS` 64,
  `MAX_BLUR_LINEAR_WORK` 16 Mpx, `MAX_BLUR_SCRATCH_BYTES` 64 MiB), a
  `Engine2dDrawIrEffectValidation` result struct, and a layered private helper
  set (`_draw_ir_effect_style_count/_value/_invalid/_positive_decimal`,
  `_geometry_valid`, `_clip_valid`, `_only_keys`) under four public entry points
  (`engine2d_draw_ir_effect_validation`, `engine2d_draw_ir_blur_linear_work`,
  `engine2d_draw_ir_blur_scratch_bytes`, `engine2d_draw_ir_rect_mask_pixels`
  and its `_clipped` variant).
- **`_draw_ir_effect_checked_product` / `_checked_sum` against
  `_ENGINE2D_DRAW_IR_I64_MAX`** — deliberate overflow-safe arithmetic. This is
  a resource-exhaustion / integer-overflow guard on GPU effect dispatch, i.e.
  security-relevant, not a sketch.
- Four accompanying specs totalling ~23 KB, one of which
  (`backend_emu_blur_rolling_spec.spl`) exercises the emulated backend.

Caveat, and the reason it is not ranked #1: it is **untracked in every copy**
and its only git backing is three *description-less jj snapshots*. Nobody ever
wrote a commit message for it, so there is no statement of intent to check the
code against, and no CI has ever seen it. Specs were **not run** (host load ~32;
running them needs a build). Its finished *shape* is established; its
*correctness* is not.

**Recommended handling (for you, not done by me):** take the copy from
`/home/ormastes/dev/pub/simple/build/worktrees/simpleos-engine2d-stage4-snapshot`,
land module + all four specs together in one described commit, and run the specs
before pushing. Do not land the module without the specs — an untested overflow
guard is worse than none.

---

# Hazards found (not work — flag before anyone syncs these)

- **`/home/ormastes/dev/pub/simple-wt-queryir`: 49,859 files show as `D`**
  (deleted) in `git status`, 16 untracked, across `src/compiler_rust` (43,185),
  `src/app`, `src/os`, `src/compiler`. This is a gutted working copy. A
  `jj commit -a` or `git add -A` here reproduces the tree-wipe that hit `main`
  twice. It holds no work; it holds a loaded gun.
- **`/home/ormastes/dev/pub/simple_release_beta2_wt`**: HEAD is 2026-07-30, WC is
  105 files at **+2,192 / −2,216**. Insertions ≈ deletions over a five-day-stale
  base is the signature of a rewind, not a fix. Do not sync.
- **`a44fd642416`** (AOP chain) is a jj conflict commit — see item 1.
- `/home/ormastes/dev/pub/simple-webrender-gpu-offload-wt`: 318 untracked, 126 of
  them `doc/09_report`. Regenerable; per instruction its plan doc was not touched.

# What could not be determined

- **Whether any class-(iii) specs pass.** No spec run was performed. Host load
  was ~32 and every candidate needs a build first; a spec run under that load
  produces exactly the SIGTERM-truncation / 60 s-timeout false results this repo
  has documented. Applicability was probed instead with `git merge-tree
  --write-tree`, which is cheap and exact for conflicts but says nothing about
  behaviour.
- **Whether the 45 contested-only worktrees are truly superseded.** Each one's
  files were independently modified at origin, so deciding needs a per-file
  both-directions diff. Given they are all small (mostly 1–4 files) and their
  subjects match commits already in origin's history, they are recorded as
  probable class (i) rather than audited individually.
- **Whether the LLVM23 and AOP lanes are still live and about to push.** Both
  have commits from within the hour of this audit. They may land on their own.

# Provenance

Working data: `…/scratchpad/audit/{uniq,clean,delta,nonancestor,damaged_scan}.txt`
and `…/scratchpad/audit/uniqfiles/*.clean` (per-worktree unlanded file lists).
