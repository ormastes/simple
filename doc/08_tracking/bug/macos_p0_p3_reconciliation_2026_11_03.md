# macOS P0–P3 reconciliation — 2026-11-03

Source baseline: `8b473cc8b35a634a291f8d815888558dd7f9fffd`, release/1.0.0.
Execution host: Linux AArch64. No native Mac or authenticated SSH target was
available to this repair lane. This report does **not** close all macOS bugs.

## Verified cross-platform runner regression

[GitHub issue #1632](https://github.com/ormastes/simple/issues/1632) reports that
M5 hermetic evidence sealed with mode 500 prevents the next persistent-runner
checkout from removing its old tree. The current `repo-hygiene.yml` already
puts both M5 advisory steps under `runner.temp`, followed by an always-run
cleanup of that exact storage root. No duplicate production fix was made.

The new case in `macos_m5_hermetic_snapshot_wrapper_test.shs` executes the real
wrapper with that external-storage contract. It verifies one successful receipt,
read-only evidence and output, absence of checkout-local storage, successful
checkout deletion and recreation, and survival of the sealed external receipt.
It never makes evidence writable to permit checkout deletion.

Executed once:

```text
sh test/01_unit/scripts/macos_m5_hermetic_snapshot_wrapper_test.shs
PASS — M5 hermetic wrapper: clean snapshot admitted; 5/5 mutations rejected; undeclared files excluded; checkout reuse preserves sealed external evidence
```

This is portable shell/filesystem regression evidence for the existing workflow
fix, not a new GitHub Actions run or a macOS bootstrap result. The canonical
registry adds `hermetic_m5_evidence_blocks_runner_checkout_2026_11_03` as fixed
at this scope. The GitHub issue remains independently managed.

## Native verification remains required

| Priority / issue | Current evidence and required next step |
| --- | --- |
| P0 `stage3_current_source_hir_rss_termination_2026_08_14` | Retained-owner/lowerer reuse repairs exist. Current provenance-bound macOS full-graph RSS acceptance is still missing. A reentrant import guard is not proof of the historical memory defect's closure. |
| P0 `stage3_macos_full_graph_hir_sigsegv_2026_09_21` | Aggregate-nil source gating is a hypothesis-specific mitigation. The original fault has no established symbolized root cause; capture it on the exact native lineage before asserting a repair. |
| P1 duplicate native-all exports | Archive owner-selection repair and portable policy evidence exist. Native macOS link/bootstrap qualification remains pending. |
| P1 test-runner process cap | Source policy is repaired; native Phase 2 test qualification remains pending. |
| Former P1 stdbuf and TMPDIR quoting | Both repairs and regression fixtures already exist; latest registry marks them fixed while the documentation preserves the native execution limitation. No repeated patch or green rerun was made. |
| P2 GPU library candidates | Target-aware source repair exists. Native library-load evidence remains pending. |
| P2 GUI activation | Cocoa activation/window ordering code and a live system scenario exist. Native window/input acceptance is not established by source inspection. |
| P2 Vulkan empty batch | Empty/zero-area guards and retained-outline repairs exist. Native provenance-bound glyph/GUI execution remains required. |
| P3 freetype workflow dependency | The workflow already installs freetype and exports library/include paths. The registry's stale `open` state is corrected to `fix-implemented-verification-pending`; no native test is claimed. |

Other P3 records concerning stale deployed tools, seed crash/fork bridges,
Stage 2 Hello/linking, Stage 3 admission and ZeroKind, and signed GUI process
evidence retain their existing unresolved status. They require exact current
native producer/runtime admission and their documented scenario, not a blanket
registry closure. A generic char-condition record mentioning a Mac workaround
is a compiler-wide issue; Metal emulation on Linux is outside a macOS repair
claim.

The registry inventory is a triage snapshot, not an exhaustive proof that no
unregistered macOS bug exists. Source-only fixes, unavailable native hosts and
historical checks remain explicitly distinct from executed acceptance.
