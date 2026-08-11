# Gate Oracle Soundness Census — 2026-08-11

Status: FIRST-PASS TRIAGE (static analysis only, not re-verified line-by-line
for every gate). See "Confidence / follow-up" section — do not treat the
per-gate bucket assignments below as final without a full manual read.

## Why this doc exists

Measured today: `bin/simple run` exits 0 after a fatal `error: semantic:`;
the `compile` lane exits 0 on `error: compile failed`; `native-build`'s
success funnel (`src/app/io/_CliCompile/compile_targets.spl:1239`) checks
only that the output file exists — an artifact with zero `FUNC` symbols
would pass and be reported `Build complete`. A prior agent counted ~26
lanes using native-build exit code as sole oracle but explicitly did not
re-verify that figure (`doc/08_tracking/bug/native_build_reports_success_for_functionless_artifact_2026-08-10.md`).
This doc re-derives the census independently.

## Method

`find scripts/check -type f \( -name '*.sh' -o -name '*.shs' -o -name '*.spl' \)`
enumerated **592 files** under `scripts/check/**`. Filtering out fixtures
left **535** real gate/helper scripts. Of those, **112** actually invoke a
build/compile/run/native-build lane (grepped for `native-build`,
`bin/simple run`, `bin/simple compile`, etc., with explicit file-list args
via xargs — never a bare `grep $(cat biglist)`, which silently returns
empty past ARG_MAX).

**Positive control:** the same lane-invocation grep pattern, restricted to
just `native-build`, hit 94/112 files — proving the search mechanics work
(a real, non-trivial hit rate) rather than degrading to a silent-empty
false zero.

## Re-derived counts vs the prior "~26" heuristic

| Class | Count (this pass) |
|---|---|
| ARTIFACT-INSPECTING | 19 |
| STDOUT-ORACLE | 7 |
| EXECUTING (asserts on actual run output/log) | ~30 |
| EXIT-CODE-ONLY (confirmed via `$?`/`rc=`/`exit_code` pattern) | ~39 |
| UNCERTAIN — needs full manual read before final bucket | 17 |
| **Total lane-invoking scripts** | **112** |
| N/A (no build/compile/run lane at all) | 423 of the 535 |

**Delta vs "~26":** the confirmed EXIT-CODE-ONLY bucket here is **~39-45**,
higher than the prior heuristic, once `bin/simple run`-only lanes (not just
`native-build`) are included. This is expected to move further once the 17
UNCERTAIN scripts are read in full — several EXECUTING-bucket entries only
became correctly classified after a manual spot-read overrode an initial
grep-only guess (e.g. `check-native-tuple-to-text.shs`, initially flagged
exit-code-only by pattern match, is actually EXECUTING once read at line 41).
This is direct evidence that **grep-pattern classification alone is not
reliable enough to gate fixes on** — full reads are required before any
gate is "fixed."

## EXIT-CODE-ONLY gates (confirmed), by consequence

### Tier 1 — bootstrap/provenance chain (worst: false-green poisons every downstream stage)
- `scripts/check/lib/bootstrap-stage3/manifest-verify.shs`
- `scripts/check/lib/bootstrap-stage3/manifest-write.shs`
- `scripts/check/lib/stage4-candidate-provenance.shs`
- `scripts/check/check-compiler-provenance.shs` *(classified ARTIFACT-INSPECTING in this pass — re-confirm; provenance claims specifically need symbol/hash inspection, not just presence-of-manifest)*

  **Recommended oracle:** artifact/symbol-table inspection (`nm`/`readelf`
  FUNC-symbol count, or content hash) of the binary produced at *each*
  bootstrap stage, not just log-line/manifest presence. A manifest that
  records "stage succeeded" without inspecting the stage's own output
  artifact is exactly the same failure shape as the native-build bug this
  census exists to catch.

### Tier 2 — native-build / link-lane parity and functional claims
- `scripts/check/check-predicate-parser-native-build.shs`
- `scripts/check/check-rocm-engine2d-font-readback.shs` (manual-review candidate, leaning EXIT-CODE-ONLY at line 80)
- `scripts/check/build-x25519mlkem768-gpu-evidence-runner.shs`
- `scripts/check/check-rv32-nvme-nand-recovery.shs`
- `scripts/check/check-simpleos-usb-xhci-qemu.shs`
- `scripts/check/check-nvme-rv32-minimal-live.shs`
- `scripts/check/check-simpleos-virtio-snd-qemu.shs`
- `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`
- `scripts/check/build-macos-gpu-2d-live-native.shs`
- `scripts/check/build-macos-full-cli-gui-provenance.shs`
- `scripts/check/check-cranelift-aot-aggregates.shs`
- `scripts/check/check-jit-unresolved-symbol-guard.shs`
- `scripts/check/check-no-jit-module-drop.shs`
- `scripts/check/check-simpleos-arm64-unified-live.shs`

  **Recommended oracle:** for lanes claiming "the build produced a working
  artifact," the cheapest sound fix is a FUNC-symbol-count check (same
  helper pattern already used by `check-native-build-artifact-has-functions.shs`,
  one of the 19 ARTIFACT-INSPECTING gates) — reuse that helper rather than
  writing 14 bespoke ones. For lanes claiming a *behavioral* result
  (e.g. GPU evidence, hardware-recovery correctness), execution + stdout/log
  assertion is the right instrument — do not substitute a symbol check for
  a behavioral claim, and don't substitute a stdout oracle for an identity
  claim (per the sibling agent's correct point that these two failure modes
  need different instruments).

### Tier 3 — misc functional/behavioral gates, exit-code-only
- `check-native-enum-match-payload.shs`, `check-native-option-try-target-fail.shs`,
  `check-startup-size-performance-audit.shs`, `check-engine-claiming-specs-use-probe.shs`,
  `check-jit-array-oob-nil-sentinel.shs`, `check-process-parent-death.shs`,
  `check-pure-simple-pipe-lambda-parse.shs`, `check-gtk-gui-size-speed-baseline.shs`,
  `check-gui-renderdoc-feature-coverage-status.shs`, `check-sspec-evidence-regeneration.shs`,
  `check-build-defaults-collect-all-and-incremental.shs`, `check-implicit-self-field-assignment.shs`,
  `check-stage4-selfhost-parse-memory.shs`, `check-heavy-work-preflight.shs`,
  `check-widget-showcase-4k-200fps.shs`, `check-simpleos-wm-host-seam-evidence.shs`,
  `check-simpleos-screen-type-qemu-evidence.shs`, `pre-push-conflict-tree-guard.shs`
  *(note: this one already emits the verdict-line convention — see below — but its
  build/compile sub-steps are still exit-code-only)*,
  `check-macos-metal-browser-backing-evidence.shs`, `check-named-ctor-unknown-field-rejected.shs`,
  `sync-native-health-guard.shs`, `check-riscv-hardware-gates.shs`,
  `check-production-gui-web-host-gpu-queue-readback-evidence.shs`,
  `check-render-perf-v-lane-suite.shs`, `check-simpleos-wm-qmp-drag-delta-evidence.shs`,
  `check-simpleos-memory-leveling-qemu.shs`, `check-untyped-list-element-shift.shs`,
  `check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`,
  `check-simpleos-screen-evidence-gate-proof.shs`, `check-try-operator-error-propagation.shs`

  **Recommended oracle:** case-by-case — most of these assert a language
  or runtime *behavior* (enum match, array OOB, try-operator propagation,
  perf), so EXECUTING + explicit output/log assertion is the fix, not
  artifact inspection. `check-startup-size-performance-audit.shs` and the
  various `*-evidence.shs` QEMU gates are borderline "evidence" gates —
  they likely already capture logs but may not be *asserting* on them
  beyond process exit; that needs the manual read below to confirm.

## UNCERTAIN — needs full manual read before final classification
`check-electron-vulkan-web-parity.shs`, `check-engine-differential.shs`,
`check-native-object-cache-granularity.shs`,
`check-linux-hosted-wm-live-window-evidence.shs` (leans ARTIFACT-INSPECTING,
sha256 check around line 128), `check-u32-array-not-packed.shs`,
`check-trait-solver-method-resolution-variant.shs`, `check-seed-extern-registry.shs`,
`check-simpleos-servers-qemu.shs`, `check-native-tuple-to-text.shs` (spot-read:
actually EXECUTING, not exit-code-only — grep-only pass mis-bucketed it).

## Verdict-line convention (`PASS — <n> ... checked` / `FAIL` / `ERROR — nothing was checked`)

Broader adoption than the "4-5 pre-push guards" framing in
`.claude/rules/vcs.md` suggests: the pattern shows up in ~90+ scripts across
`scripts/check/**`, not just the pre-push guards. It is closer to an
emerging house style than a guard-specific convention. Exact count of
lane-invoking gates that *lack* it entirely (the ones most worth retrofitting
first, since a missing verdict line compounds with an unsound oracle) was
not fully computed this pass — follow-up: intersect the 112 lane-invoking
list against verdict-line grep hits.

One concrete finding: `scripts/check/pre-push-conflict-tree-guard.shs`
emits the verdict-line convention at its top level, but internally still
treats a build/compile sub-step's exit code as sufficient — the convention
covers the guard's own PASS/FAIL, not the soundness of what it measured.

## Prioritised worklist (worst consequence first)

1. **Bootstrap/provenance chain** (`lib/bootstrap-stage3/manifest-verify.shs`,
   `manifest-write.shs`, `lib/stage4-candidate-provenance.shs`,
   `check-compiler-provenance.shs`) — false green here silently poisons every
   downstream stage build. Retrofit: per-stage symbol/hash inspection.
2. **Native-build/link-parity Tier 2 list above (14 gates)** — retrofit with
   the existing `check-native-build-artifact-has-functions.shs` FUNC-symbol
   helper rather than bespoke checks.
3. **17 UNCERTAIN gates** — full manual read first; do not guess bucket.
4. **Remaining Tier 3 exit-code-only gates (~30)** — batch review, apply
   EXECUTING or ARTIFACT-INSPECTING oracle per the specific claim each gate
   makes; do not blanket-apply one instrument to all of them.
5. **Verdict-line retrofit** — once oracle soundness is fixed, add the
   `PASS — <n> checked` / `FAIL` / `ERROR — nothing was checked` convention
   to any of the above still missing it, matching the house standard already
   used by the pre-push guards.

## Confidence / follow-up

This is a grep-assisted first pass, not an exhaustive read of all 112
lane-invoking scripts. Several initial grep-pattern buckets were wrong on
manual spot-check (see `check-native-tuple-to-text.shs` above), which is
itself evidence that a dedicated follow-up pass — reading each of the 112
scripts in full, not pattern-matching — is required before any individual
gate is "fixed." Do not use the per-script bucket assignments above as a
final work-authorization list without that read. The real pre-push hook
dispatch path (`scripts/hooks/pre-push` vs `.git/hooks/pre-push` vs the
standalone `pre-push-conflict-tree-guard.shs`/`check-no-conflict-*.shs`
scripts) was also not fully traced — flagged for follow-up, not resolved
here.
