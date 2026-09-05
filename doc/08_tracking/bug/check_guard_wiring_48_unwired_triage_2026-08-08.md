# Triage of check-guard-wiring.shs unwired guards (2026-08-08)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

REPORT-ONLY. No guard was wired, deleted, or edited. `scripts/check/check-guard-wiring.shs`
was run unmodified from the repo root and its verbatim output was used as the source of
truth.

## Environment check

`git rev-parse --show-toplevel` resolved correctly to `/home/ormastes/dev/pub/simple`
(`git rev-parse --is-bare-repository` = `false`, `pwd -P` matched the resolved toplevel).
The stray `core.worktree`/`core.bare` pathology described in
`doc/08_tracking/bug/shared_git_config_core_worktree_misdirects_prepush_guards_2026-08-08.md`
was NOT present at the time of this run. Not touched either way, per instructions.

## Count drift vs. the source bug report

The bug report this task cites
(`doc/08_tracking/bug/guard_fixtures_missing_locally_silently_disable_prepush_checks_2026-08-08.md`)
recorded `FAIL — 476 guard(s) checked, 48 unwired, 0 bad opt-out(s), 0 copied hook(s)`.
This run, same day, same unmodified script, produced:

```
check-guard-wiring: selftest 8/8 fixtures correct
guard_total=480
guard_invoked=86
guard_orphaned=394
guard_optout_listed=342
installed_hooks=3
installed_hooks_not_symlink=2
guard_wiring_ok=false
check-guard-wiring: FAIL — 480 guard(s) checked, 52 unwired, 0 bad opt-out(s), 2 copied hook(s)
```

Guard total rose 476→480 (4 new guard scripts landed since the cited report) and unwired
rose 48→52 (4 more entered the unjustified set — consistent with new guards being added
without being wired or opted out, exactly the failure mode this script exists to catch).
Two installed hooks (`pw_patterns.txt`, `secrets.patterns`) are now flagged as non-symlink
copies; these are pattern-data files, not guard scripts, and are out of scope for this
triage (separate lane, not touched).

This report triages the **current 52**, which is a strict superset of the **48** referenced
in the task (all 48 are almost certainly still present under different surrounding counts;
no attempt was made to diff which exact 4 are new, since the task's classification goal is
unaffected by the count drift). All 52 are listed below with full classification.

## Method

For each of the 52 `unwired_guard=` names:
1. Confirmed via `grep -rl <name> .github/workflows` that none are invoked from any GitHub
   Actions workflow (0/52 hits) — this matches the wiring script's own "roots" scan, which
   already includes `.github/workflows` as a root directory, so a script the wiring scan
   calls orphaned cannot simultaneously be CI-invoked under the same textual-match model.
   **Result: zero CI-ONLY guards in this set** — the CI-ONLY category is empty by
   construction for anything this script reports orphaned.
2. Read each script's header comment and scanned full file text for classification signals:
   `fail-closed`, `critical`, `flight`, `safety`, `diagnostic-only`, `manual`, `on-demand`,
   `requires hardware/board/qemu`.
3. Checked whether the guard's target subsystem still exists in the tree (none were found
   to reference a deleted subsystem — see SUPERSEDED/DEAD notes below).

## Classification counts

| Classification | Count |
|---|---|
| CI-ONLY | 0 |
| GENUINELY ORPHANED | 49 |
| SUPERSEDED/DEAD | 0 (candidate, not confirmed — see note) |
| INTENTIONALLY MANUAL | 3 |

Note on SUPERSEDED/DEAD: none of the 52 guard scripts were found to check a subsystem that
has been deleted from the tree — every referenced doc/plan path or subsystem name resolved
to something still present. This is a lower-confidence negative (a full "does the checked
*behavior* still exist" audit per guard was out of scope at this effort level); flag as
"none confirmed" rather than "zero, verified."

## Full table (52 rows)

| Guard | Classification | Reason | Risk note |
|---|---|---|---|
| build-mlkem-simd-c-lane.shs | GENUINELY ORPHANED | Builds/runs ML-KEM NTT SIMD C lane from committed sources; heavyweight build lane, no manual-only statement in header | Post-quantum crypto lane — SAFETY/SECURITY-relevant |
| check-array-remove-returns-element.shs | GENUINELY ORPHANED | Regression guard: `array.remove(index)` must mutate+return in place, every engine | Correctness-critical (silent semantic divergence across engines) |
| check-backend-evidence-branch-coverage.shs | GENUINELY ORPHANED | Validates backend evidence checker coverage from LCOV branch data only | Measurement-integrity guard |
| check-bootstrap-platform-handoff-readiness.shs | GENUINELY ORPHANED | "Read-only, fail-closed readiness checker for the bootstrap platform handoff" | **fail-closed** — bootstrap path, high blast radius |
| check-cpu-backend-artifacts.shs | GENUINELY ORPHANED | Validates CPU backend build artifacts | Build-integrity |
| check-engine2d-jit-timing.shs | GENUINELY ORPHANED | Unit B2 of render_2d Vulkan coverage plan — JIT timing baseline; plan-milestone unit, not declared manual-only | Perf regression only, not safety |
| check-env-get-dead-fallback-guard.shs | GENUINELY ORPHANED | Positive control for the DEAD-FALLBACK half of the `rt_env_get` `??` bug family | Correctness-critical (silent dead-fallback masking real values) |
| check-env-get-nil-abort-guard.shs | GENUINELY ORPHANED | Positive control for silent function-abort family rooted in `rt_env_get` | **Correctness-critical** — silent abort = swallowed failures |
| check-for-loop-variable-scoping.shs | GENUINELY ORPHANED | `for` loop var must not leak/clobber outer scope, every engine | Correctness-critical |
| check-freebsd-wm-seam-refusal.shs | GENUINELY ORPHANED | In-VM FreeBSD verification (Task 60 Lane B); heavyweight VM lane, not in opt-out despite matching the opt-out's own stated criteria | Requires FreeBSD VM — same class as seeded opt-out entries but never added |
| check-gpu-backend-layer-evidence.shs | INTENTIONALLY MANUAL | Header text contains "diagnostic-only" for the runtime/device admission stage; artifact-first evidence gate deliberately staged | Legitimate — matches opt-out program's stated criteria |
| check-gpu-runnable.shs | GENUINELY ORPHANED | Repo gate for `gpu_runnable_scan.spl` transitive scanner, `--summary WARN...` mode | Lightweight enough it could likely be wired cheaply |
| check-implicit-self-field-assignment.shs | GENUINELY ORPHANED | Bare `field = value` in a method must HARD ERROR, never silently no-op | **Correctness-critical** — silent write loss is a classic data-corruption class |
| check-jit-array-oob-nil-sentinel.shs | GENUINELY ORPHANED | Regression canary for JIT array OOB-read raw-sentinel leak | **Correctness/safety-adjacent** — OOB read leaking raw sentinel values |
| check-lexer-radix-literal-suffix.shs | GENUINELY ORPHANED | Executable fence for a specific lexer commit pair, adversarially reviewed | Narrow scope, low blast radius |
| check-lint-binary-staleness.shs | GENUINELY ORPHANED | Staleness probe for deployed lint oracle (`bin/simple`/`bin/release/.../simple`) | **Meta-guard** — matches memory's recorded "sabotage is not an oracle for lint / deployed binary is stale" trap |
| check-named-ctor-unknown-field-rejected.shs | GENUINELY ORPHANED | Named-ctor arg with no matching field must be a compile error | Correctness-critical |
| check-native-enum-match-payload.shs | GENUINELY ORPHANED | AOT/LLVM payload-bearing enum `match` regression gate | Correctness-critical, matches memory's "match on enum has no native lowering" family |
| check-native-extern-fabrication.shs | GENUINELY ORPHANED | AOT host-target `@extern fn` fabrication regression gate | **Correctness-critical** — fabricated/stub externs masquerading as real bindings is exactly the class flagged elsewhere as a fail-open risk |
| check-native-object-cache-granularity.shs | GENUINELY ORPHANED | native-build object cache fingerprint granularity canary | Build-correctness (stale-cache reuse risk) |
| check-native-option-bool-eq-vs-literal.shs | GENUINELY ORPHANED | AOT `Option<bool>` vs raw bool/nil literal equality regression | Correctness-critical |
| check-native-option-eq-representation.shs | GENUINELY ORPHANED | AOT inlined `Option<text>` return equality regression | Correctness-critical |
| check-native-utf8-slice.shs | GENUINELY ORPHANED | AOT/JIT-vs-interpreter UTF-8 mid-codepoint slicing divergence | Correctness-critical, matches memory's "native slice splits UTF-8, no validation" |
| check-no-jit-module-drop.shs | GENUINELY ORPHANED | "fail-closed fence against paren-less accessors... silent ~100-1000x whole-module deopt" | **fail-closed**, severe perf cliff, silent |
| check-no-sabotage-residue.shs | GENUINELY ORPHANED | Detects unrestored verification markers left by sabotage-verification cycles | **Meta-guard** protecting verification integrity itself |
| check-pure-simple-pipe-lambda-parse.shs | GENUINELY ORPHANED | Parse gate: pure-Simple frontend must accept pipe-lambda form | Language-frontend correctness |
| check-render2d-container-suite.shs | GENUINELY ORPHANED | Unit B3 of render_2d Vulkan coverage plan — container-run verification | Plan-milestone unit, no manual-only statement |
| check-render2d-coverage.shs | GENUINELY ORPHANED | "Fail-closed prerequisite gate" for render_2d Vulkan Wave-3 (C1-C3) | **Fail-closed** header tag |
| check-render-perf-v-lane-suite.shs | GENUINELY ORPHANED | V-lane correctness/promotion suite, render-perf redesign campaign | Campaign-specific, perf/correctness |
| check-simpleos-io-audio-qemu.shs | GENUINELY ORPHANED | QEMU virtio-snd/io audio boot evidence; mentions "flight" in header text | Requires QEMU; heavyweight-evidence class, not opted out |
| check-simpleos-native-board-gpu-2d.shs | GENUINELY ORPHANED | "Fail-closed native-board GPU evidence gate... bounded dispatcher until board-sp[ecific]..." | **Fail-closed**, board-runnable-rule relevant |
| check-simpleos-screen-evidence-gate-proof.shs | GENUINELY ORPHANED | Proves the `simpleos_screen_*` evidence gate itself fails closed | **Meta-guard** — a gate that proves another gate is not vacuous |
| check-simpleos-screen-type-qemu-evidence.shs | GENUINELY ORPHANED | Per-screen-type (wm/2d/web/gui) QEMU boot evidence, "FAIL-CLOSED" tag | **Fail-closed**, QEMU-dependent |
| check-simpleos-virtio-snd-qemu.shs | GENUINELY ORPHANED | virtio-snd QEMU boot check | Requires QEMU |
| check-simpleos-wm-host-seam-evidence.shs | GENUINELY ORPHANED | WM host seam evidence gate | Heavyweight evidence producer |
| check-spec-runner-tail-expression-verdict.shs | GENUINELY ORPHANED | Positive control for two spec-harness false-verdict mechanisms the spec corpus can't police itself | **HIGH — meta-guard for measurement integrity**; matches memory's "harness contradicts itself" family, false verdicts poison every other spec's trust |
| check-test-tree-divergence.shs | GENUINELY ORPHANED | Fails when a mirrored test-tree path diverges from canonical, "FAIL-CLOSED" tag | Repo-hygiene, fail-closed tag |
| check-trait-solver-method-resolution-variant.shs | GENUINELY ORPHANED | Trait solver must return a variant, never a field bag; tied to `primitive_receiver_trait_impl...` bug doc | Correctness-critical, matches memory's "impl Trait for primitive never dispatches" family |
| check-try-operator-error-propagation.shs | GENUINELY ORPHANED | `?` operator must early-return on Err, tied to `try_operator_early_return...` bug doc | **HIGH — matches memory's recorded live defect** "`?` early-return matches NEITHER Ok NOR Err — Err silently lost, rc=0" |
| check-tuple-index-out-of-range.shs | GENUINELY ORPHANED | Compile-time-constant OOB tuple index must be compile error, not silent OOB heap read | Correctness/memory-safety-adjacent |
| check-ui-showcase-layering.shs | GENUINELY ORPHANED | Enforces SimpleOS UI-showcase layering rule, "FAIL-CLOSED" tag | Fail-closed, architecture-boundary |
| check-untyped-list-element-shift.shs | GENUINELY ORPHANED | Untyped `list`-param element-read `<<3` corruption (Rust seed JIT lane) | **HIGH — matches memory's recorded live defect** "list.get << 3" |
| check-use-warning-oracle-deployed.shs | GENUINELY ORPHANED | Refuses a deployed `bin/simple` whose `[use-warning]` oracle is missing/noisy | **HIGH — meta-guard**, matches memory's "unresolved use is only a warning, fail-open" trap |
| check-utf8-slice-audit-live.shs | GENUINELY ORPHANED | Refuses to trust a UTF-8 slice-boundary measurement from an uninstrumented binary | **Meta-guard** for measurement integrity, same family as native-utf8-slice defect |
| check-vacuous-specs.shs | INTENTIONALLY MANUAL | Header/body explicitly say "fail-closed detector for non-discriminating specs" with explicit "manual" language found in text | Legitimate — large/slow full-corpus scan class |
| check-virtio-gpu-capset-qemu.shs | GENUINELY ORPHANED | QEMU virtio-gpu headless smoke test (Unit V3), "Fail-closed" tag | Requires QEMU/GPU |
| check-wm-host-css-override-evidence.shs | GENUINELY ORPHANED | Drives the existing production fullscreen launcher twice to prove CSS-override evidence | Heavyweight evidence producer, drives production code paths |
| check-wm-lane-boundary.shs | GENUINELY ORPHANED | WM/GUI/web/2D portable-lane dependency boundary gate, "Fail-closed" tag | Architecture-boundary, fail-closed |
| check-x25519mlkem768-cuda-ntt.shs | GENUINELY ORPHANED | X25519+ML-KEM768 hybrid PQ-crypto CUDA NTT correctness check | **HIGH — SECURITY-critical**: post-quantum crypto NTT correctness on CUDA backend |
| check-x25519mlkem768-vulkan-ntt.shs | GENUINELY ORPHANED | Same, Vulkan backend | **HIGH — SECURITY-critical**: post-quantum crypto NTT correctness on Vulkan backend |
| replay-llvm-artifact.shs | GENUINELY ORPHANED | Replay tool for an LLVM artifact (utility, not a `check-` prefixed guard) | Utility/tooling, lower risk |
| stage4-diagnostic-two-phase.shs | INTENTIONALLY MANUAL | Header explicitly: "Diagnostic-only Stage 4 corpus sweep" | Legitimate — named diagnostic, not a gate |

## Ranked top-10 "wire these first" (GENUINELY ORPHANED, safety/correctness-relevant, ranked by risk)

1. **check-try-operator-error-propagation.shs** — guards a *known, currently-recorded* live
   defect (memory: `?` early-return matches neither Ok nor Err, Err silently lost, rc=0).
   Zero coverage today means this exact regression could reappear undetected.
2. **check-untyped-list-element-shift.shs** — guards a *known, currently-recorded* live
   defect (`list.get << 3`). Same reasoning as #1.
3. **check-x25519mlkem768-cuda-ntt.shs** — post-quantum crypto correctness (CUDA). Silent
   NTT corruption in a crypto primitive is a security-grade risk.
4. **check-x25519mlkem768-vulkan-ntt.shs** — same, Vulkan backend.
5. **check-spec-runner-tail-expression-verdict.shs** — meta-guard for spec-harness
   false-verdict mechanisms; unwired here means every OTHER spec's "verified" claims are
   less trustworthy tree-wide.
6. **check-use-warning-oracle-deployed.shs** — meta-guard against a recorded fail-open
   trap (`use` warnings). Directly protects the reliability of every other lint-based check.
7. **check-native-extern-fabrication.shs** — guards against fabricated/stub `@extern`
   bindings masquerading as real ones under AOT — a "looks-wired-but-isn't" failure class.
8. **check-implicit-self-field-assignment.shs** — silent field-write no-op is a classic
   data-corruption class that would otherwise surface only as unrelated downstream bugs.
9. **check-no-jit-module-drop.shs** — fail-closed fence against a documented silent
   100-1000x perf cliff; not memory-unsafe but severe and silent.
10. **check-env-get-nil-abort-guard.shs** — guards silent function-abort on a core runtime
    primitive (`rt_env_get`); silent aborts can mask failures across many call sites.

## MANIFEST

```
doc/08_tracking/bug/check_guard_wiring_48_unwired_triage_2026-08-08.md
```

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (census, no fix claimed).** Confirmed as a triage document; the unwired
set was re-measured, not reduced. Same family as `check_script_wiring_orphans_2026-08-01.md`
— these two rows collapse into one backlog item (wire or retire the orphan guards), not two bugs.
Note: this lane ADDED one new guard, `scripts/check/check-phantom-log-reference.shs`, which is
currently itself unwired and should be added to a caller when the wiring backlog is worked.
