# Main integrity & backlog — single plan

**Owner lane:** cross-cutting (guards/gates, stale-merge recovery, bootstrap, bug backlog).
**Opened:** 2026-09-07. **Baseline:** `origin/main` = `7c87c9cda85`, 17 open PRs.
**Evidence report (what happened, not what to do):** `doc/09_report/todo_bug_triage_this_linux_2026-09-06.md`.

This is the ONE place. Everything actionable that came out of the 2026-09-06/07
triage lives here, in priority order. Each item states its next concrete action,
its blocker, and how to know it is done.

---

## 0. Host capability — the filter for everything below

| Capability | State | Consequence |
|---|---|---|
| arch | **aarch64** | x86_64-only lanes (OVMF/nvfs) cannot run here |
| `bin/simple` | **Rust seed** only | no self-hosted full CLI; Stage 3/4 lanes gated |
| cargo / rustc | present | seed work and `cargo check` (~1 min warm) are fast |
| clang | `~/dev/llvm/install/bin/clang` | C-runtime gates runnable |
| GPU | NVIDIA GB10 + `nvcc` | GPU rows unusually actionable here |
| `qemu-system-*` | **absent** | every QEMU/EFI boot lane blocked |
| SDL2 | absent, no sudo | see item 4 |
| libtorch | absent | ML live-capture blocked |

---

## 1. METHODOLOGY — read before touching any gate

Non-negotiable, learned expensively on 2026-09-06:

1. **Run gates from a clean detached checkout of the sha under test:**
   `git worktree add --detach <dir> <sha>` then run inside it. Run bare from a
   working copy and 20+ `tree`-mode rows read the WRONG TREE. This caused a real
   incident: a stale checkout made the hook report on content that was not being
   pushed while missing two genuine blocking regressions in content that was.
2. **A fixture must prove the two paths DISAGREE**, and there are **two rot axes**:
   scan-root rot *and* baseline-only rot. A fixture covering only the first missed
   the second on `rt-src-list`. Inject both, always.
3. **Byte-match before every push.** Each manifest row's `id:mode:command` must
   byte-match a case arm in `run_manifest_push_gates`
   (`scripts/check/check-push-must-pass.shs`). An unmatched row hits the
   fail-closed `*)` arm and **blocks every push from every session on this box.**
4. **`check-no-conflict-tree-push.shs` hard-caps at 64 commits** and returns
   `ERROR — nothing was checked` above it. Split and say so, or apply its own
   top-level `.jjconflict-*` test across every commit yourself.
5. **Pushes from this account BYPASS the ruleset** (`current_user_can_bypass:
   always`; verbatim `remote: Bypassed rule violations`). Required CI checks do
   NOT run on a direct push. **Local gates are the only verification.** Treat that
   as a reason for more rigour, not less.
6. **Verify the premise at dispatch time.** Three tasks on 2026-09-06 were
   dispatched against stale state (a duplicate of an open PR, a PR already merged,
   a blocker another lane had already fixed). `main` moves constantly.

---

## 2. Recover work still missing from `main` — HIGHEST VALUE

Landed work silently erased by stale merges. Audit:
`doc/09_report/stale_merge_line_loss_audit_2026-09-06.md`.

**Status:** exposure re-measured **947 lines / 94 files**; 3 recovery pushes
landed; **residual ≈845 lines / 82 files**.

Recovered so far: PR #270 (`check-repo-hygiene` 63 violations → 8), PR #277
(`cargo fmt --check` exit 1 → 0), PR #305 half (spec had survived while its
source had not: 0 passed → 1 passed).

**Next actions, in order:**
- [ ] `#265/#272/#291/#295/#298/#307` — ~120 lines of HIR/MIR lowering, 15 files.
      **Blocked on a Stage 3 run** (see item 4). Unblocks together with it.
- [ ] `#262` — 6 files, ~304 lines (`mount_table.spl`, nvfs OVMF gate).
      **Blocked: needs x86_64 OVMF**, host is aarch64. Needs another host.
- [ ] `#271` — `mem_snapshot.rs` + `native_all/lib.rs`, 31 lines. Restoring
      reddens the rt-dual ratchet; the divergence is live but the link failure
      does not reproduce. **Runtime lane's call** — see item 3's scope hole.
- [ ] `#302/#304/#306` — guards that are **non-discriminating** (exit 0 either
      way). Restoring proves nothing; fix the guards first or drop the rows.
- [ ] `#270` residue — `bootstrap-stage3-provenance-verifier.shs`: tip `.sh` is
      484L vs the lost 386L and a live consumer names `.sh`. Adjudicate.
- [ ] **Widen the census.** Two classes the original signature cannot see:
      **resurrections** (the merge revived 4 files `main` had deleted, incl.
      `mem_snapshot_provider.rs`, 438 lines) and **157 files tree-wide still
      byte-identical to the merge base**. Signature W (merge result matches
      NEITHER parent) found 56 merges / 1,942 lines — measure its false-positive
      rate before acting on it.

**Done when:** residual is zero or every remaining line has a named blocker and an
owner lane.

---

## 3. Gate & guard integrity — gates reporting green while checking less

**Landed:** 4 `tree`→`ref` conversions with fixtures; duplicate
`push-ui-slim-closure` row removed; `no-direct-rt` baseline tightened
7776 → **6072** (it had **1,704 sites of slack** and was printing
`note: forbidden count improved` on every run); `check-guard-wiring` now credits
bootstrap-tier execution (unwired baseline 734 → **725** — 9 guards CI really runs
had been recorded as debt).

**Open, from `doc/08_tracking/bug/guard_wiring_credits_dead_dispatch_arms_2026-09-07.md`
and `push_gate_tree_mode_row_census_2026-09-06.md`:**
- [ ] **20+ `tree`-mode rows still read the working checkout.** Per-row plans are
      in the census. Two have settled designs: `guard-wiring` switches enumeration
      to `git ls-tree`; `sffi-v2` uses `git worktree add --detach` and must gain
      the selftest it has never had. Prioritise **blocking** rows.
- [ ] **5 dead dispatch arms** still present (4 no-manifest-row, 1
      duplicate-shadowed). Removing them exposes 3 guards as unwired — those 3 are
      genuinely run at bootstrap tier, so credit that rather than baselining.
- [ ] **Reachability is TEXTUAL — a mention is an edge.** A prose comment naming a
      guard basename forged wiring for 10 guards (self-caught during the fix).
      Needs real reachability, not grep.
- [ ] **Duplicate `push-rt-api-groups` manifest rows** (32/36) — the gate runs
      twice per push, with differing descriptions.
- [ ] **`rt-dual` scan scope omits `src/compiler_rust/native_all`** — 18 `rt_*`
      there, only 3 baselined; widening costs ~14 new reds.
      `rt_phase_profile_record` is a false single-lane because of this.
- [ ] **Two blocking gates red on pristine `main`:**
      `push-interpreter-extern-registry-gap` (2 new — fixed in source by PR #370,
      needs a seed redeploy) and `push-sffi-v2-authority` (12 of 46).
- [ ] **`check-seed-builds-push.shs` verdict claims "test targets compile
      cleanly"** — verify that is true; `cargo check --bin simple` passing is not
      the same thing (see item 5).

**Done when:** every push-tier row reads the pushed commit, every conversion has
both rot fixtures, and no gate's verdict text overstates its scope.

---

## 4. Bootstrap / self-hosting chain

**Progress 2026-09-06:** Stage 1 PASS → Stage 2 PASS (825 files, ~704s) → a
**proven working Stage 2 binary** (compiles and runs hello world, rc=0). The Stage
3 parser gap for `pattern -> expr` match arms is **fixed and landed**
(`0f54654535d`) — the parser was wrong, ~87 such arms predate the break, and the
24 arms were correctly NOT rewritten.

**Current blocker:** Stage 2 builds, then fails its own sanity gate with
`native-capsule-source-mutated:…hello_world` — parse/hir/mono/mir/native_cache all
complete. Not parse, not SDL2. Stage 3 never reached.

- [ ] Diagnose the capsule hash mismatch: genuine mutation (something rewriting
      sources mid-build) vs false positive (path normalisation, line endings, a
      file read twice, cache scope). **Show both hashes and their inputs.**
- [ ] **Fix the wrong-log diagnostic.** The wrapper's `UNDIAGNOSABLE … NO
      diagnostic text` verdict reads `stage2-native-build.log`; the real error is
      in `stage2-receiver.log` / `stage3/<triple>/stage2-sanity.env.frontend-failure.log`.
      **This has hidden a real error twice.** Cheap, permanently valuable.
- [ ] **`-lSDL2` is appended unconditionally on Linux** at
      `native_linking.spl:346`; the Rust seed's linker never does. Worked around
      with an opt-in symbol-less stub (`SIMPLE_BOOTSTRAP_SDL2_STUB=1`), **not
      fixed**. Gate the flag on actual SDL usage.
      Record: `doc/08_tracking/bug/bootstrap_stage2_selfhost_link_requires_sdl2_2026-09-06.md`.
- [ ] Then Stage 3 → Stage 4. Stage 3 parse alone was ~4,119s for 1,085 files
      (~3.8s/file); budget accordingly. **Never deploy** — do not touch the shared
      `bin/simple` or `bin/release/**`; ~10 sessions depend on them.

**Done when:** a self-hosted full-CLI binary exists, or each remaining stage has a
measured, named blocker.

**Unblocks:** item 2's HIR/MIR rows, 5 bug rows and 2 todo rows gated on a
self-hosted binary, and `bin/simple` finally being the sanctioned tool per
CLAUDE.md rather than the seed.

---

## 5. Build & test health

- [ ] **`cargo test --release -p simple-compiler` did not compile at `main`**
      (E0428 duplicate fixture in `wsffi.rs`; two E0599). Re-verify — a grep at
      `60479fbf013` suggested part may be fixed. `cargo check --bin simple` passes,
      which is why nothing caught it.
- [ ] **Never delete a test to fix a duplicate-name error.** Read both; rename so
      both survive. If an E0599 pins an API the code lost, the CODE is wrong.
- [ ] Deploy a seed built from ≥ `1bd13da6125` so PR #370's interpreter-extern
      registration takes effect (`dynamic_loader_spec` reports 3/4 until then) and
      `push-interpreter-extern-registry-gap` goes green.

---

## 6. Silent auto-merge damage — DETECTOR LANDED 2026-09-07 (advisory)

Two confirmed instances on 2026-09-06, **neither with conflict markers**:
`source_facts.spl` (symbols used with no definitions, OUTSIDE the markers) and
`gpu_provider_probes.spl` (add/add, silently dropped main's `session.retain()`).

No existing gate can see this: markers-gate reads literal `<<<<<<<`, tree-gate
reads `.jjconflict-*`, size-gate bands file counts, api-regression tracks `rt_*`
deletions. A well-formed, correctly-sized, non-conflicted, symbol-preserving merge
result passes all of them while being broken.

- [ ] Detector candidate: *a merge result referencing a symbol defined in neither
      parent nor itself* — both incidents fit.
- [ ] **Measure the false-positive rate on real history BEFORE proposing
      enforcement.** A detector that cries wolf gets routed around with
      `--no-verify`, which is worse than no gate. Land advisory with the
      measurement if the rate is high.

---

## 7. The remaining bug/todo backlog

From the triage report. **These counts are inflated** — sampling says a large share
is already fixed or misfiled:

| Package | Rows | P0/P1 | silent-wrong-answer |
|---|---:|---:|---:|
| stdlib `src/lib/**` | 298 | 61 | 18 |
| seed-rust `src/compiler_rust/**` | 172 | 61 | 24 |
| apps/tooling | 142 | 25 | 16 |
| tests/docs/scripts | 124 | 13 | 10 |
| native codegen (50/60/70) | 111 | 45 | 11 |
| hir/types/surface | 56 | 17 | 4 |
| frontend parse+lex | 47 | 12 | 4 |
| driver/bootstrap/tools | 38 | 8 | 7 |
| interpreter eval | 33 | 11 | **10 (30%)** |
| runtime C / `rt_*` | 30 | 10 | 1 |

**Three independent samples agree the DB overstates itself:** 8 of 15
verification-pending rows were already fixed; 5 of 45 codegen P0/P1 rows were
already fixed in tree; 11 of 16 seed-rust rows were NOT reproducible.

- [ ] **Verify before fixing.** A stale-status sweep closes rows at a fraction of
      the cost of fixing them. Harnesses exist:
      `scripts/check/stale-status-sweep.shs`, `stale-status-classify.shs`.
- [ ] **210 of 260 actionable todos are P3 spec placeholders** for unimplemented
      features (set literals — DONE, SSR, hydration, structural diff, async
      `Task`). This is a **feature backlog wearing a TODO costume**; disposition it
      in bulk as a product decision, not 210 fixes. Set literals were the pilot:
      implemented, not deleted.
- [ ] Highest density, not highest count: **interpreter (30% silent)** and
      **native codegen (41% P0/P1)** — 144 rows holding 56 P0/P1s.

---

## 8. Held / deliberately not landed

| Item | Reason |
|---|---|
| PR #319 | author's own body says "do not merge yet" |
| PR #452 | open, CI-queued — the honest-opt-out reasoning for the stdlib registry script |
| `work/ui-layout-flex-units-2026-09-06` | **duplicate** — `main` is a strict superset; landing it would be a rewind |
| `#271` mem_snapshot restore | reddens rt-dual; runtime lane's call |

---

## Conventions for anyone picking this up

- Land via PR when there is no urgency (CLAUDE.md); direct push only when the
  queue is genuinely blocking and the local gates have been run properly.
- `--no-verify` is currently REQUIRED for direct pushes because the local hook
  evaluates the working checkout for 20+ rows — that is a defect being fixed in
  item 3, not a licence.
- Nothing is dropped: fix a defect while keeping the feature. If the only fix you
  can see removes a feature, that is not a fix — report it.
- Never convert a TODO/FIXME to a NOTE. Implement it or delete it deliberately.
- `doc/08_tracking/bug/bug_db.sdn` carries a `#sdn-crc32` header — never hand-edit;
  record outcomes in each bug's `.md`.

### §6 update 2026-09-07 — landed

`scripts/check/check-merge-content-conservation-push.shs`, wired advisory
(`push_blocking=false`). Record: `doc/08_tracking/bug/merge_automerge_silent_content_loss_2026-09-07.md`.

**Two corrections to §6 as originally written:**
- The proposed invariant ("a symbol referenced in neither parent nor the result")
  **does not work** — it misses the real incident, because a dropped *call* leaves
  no dangling reference. Shipped instead as two layers: **A** add/add conservation
  (base absent ⇒ `(lines(P1) ∪ lines(P2)) \ lines(result)` must be empty) and
  **B** definition conservation (a declaration a parent had, absent from the
  result, still freely called there).
- **`source_facts.spl` is NOT in committed history** — caught pre-commit by a
  human. A push gate would never have seen it. The class has ONE historical
  instance, not two.

`gpu_provider_probes.spl` proven to be git's own automatic resolution, not a hand
edit: `merge-tree --write-tree` on `7d40e71aa9c` replays the recorded blob
byte-identically with `Auto-merging` and 0 markers.

FP rate measured by controlled before/after on one 52-merge range:
**82 findings in 27 merges → 37 in 13**, Layer A byte-identical across the change
(76 = 76). 4/4 sampled Layer A findings genuine. Advisory because it is honestly
red on main's own history, intent needs a human, and no scoped-delta helper exists
yet — promotion criteria in the record.

**Follow-up carried into §3:** the `check-no-conflict-tree-push.shs` 64-commit cap
(`MAX_PUSH_COMMITS` at `:77,222,242`) — the real cost bound is **unique trees, not
commits** (the scan dedupes), so raising it is likely safe, but it needs its own
selftest. Filed, not half-landed.
