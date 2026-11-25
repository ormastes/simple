# A hardware-gated spec whose only example is `skip_if`-skipped reports file-level FAIL, not SKIP
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-11
**Found by:** two lanes writing forward-looking hardware-gated system specs, independently
**Severity:** Medium — undermines the whole point of "write the test now, it goes green when hardware lands"

## Symptom

Four new specs under `test/03_system/os/vulkan/` each contain exactly one `it`
block gated by `skip_if(condition, reason)` where `condition()` is currently
true (no matching hardware/build present). The `it`-level output correctly
shows the skip and the reason text, e.g.:

```
it proves the Gen12 encoder against real i915 hardware, not just self-comparison
  ... skipped (No Intel i915 GPU present on this host — see
  doc/08_tracking/bug/cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md)
```

But `bin/simple test <spec>` reports the FILE-level verdict as:

```
Results: 1 total, 0 passed, 1 failed
reason=zero-examples
```

A skipped example is counted as `executed=0`, and the runner's zero-examples
guard — which exists to catch a genuinely broken spec that loaded but ran
nothing — cannot distinguish that from "the one example present was correctly
skipped by design". Both look identical from outside: one example declared,
zero executed.

## Why this matters here specifically

This affects a family of specs whose entire purpose is: exist today in a
harmless SKIP state, and flip to a real PASS with zero code changes the day
specific hardware or a build flag becomes available
(`board_vulkan_intel_gen12_submit_readback_system_spec.spl`,
`board_vulkan_adreno_submit_readback_system_spec.spl`,
`board_vulkan_img_bxe_submit_readback_system_spec.spl`,
`board_vulkan_venus_qemu_submit_readback_system_spec.spl`). A file-level FAIL
sitting in the tree reads as "this test is broken", not "this test is
correctly waiting for hardware" — which is the opposite of the intent, and
would mislead anyone scanning for red specs into treating a deliberate,
documented gate as a regression.

## Scope

Confirmed on 4 new files plus at least one pre-existing sibling using the
identical single-`it`-plus-`skip_if` shape, so this is a general runner gap,
not specific to these four files.

## Unblock condition

The test runner should treat "declared == 1, executed == 0, all-skipped == 1"
as a distinct, non-failing verdict (e.g. `SKIPPED`) rather than folding it into
the same `reason=zero-examples` bucket used for a spec that loaded but
genuinely ran nothing due to a defect. The two cases are semantically opposite
(intentional deferral vs. accidental no-op) and should not share one failure
code. A spec with N>1 examples where some are skipped and at least one executes
already reports correctly — this is specific to the all-skipped, N=1 case.

## Status

Open. Filed rather than worked around: the four hardware-gated specs are left
as written (correct `it`-level skip behavior, correct reason text) since
rewriting them to dodge this runner quirk (e.g. padding with a dummy always-run
example) would obscure their actual purpose. The file-level FAIL is a known,
accepted cosmetic issue until the runner is fixed.


## Resolution 2026-11-25 (work/p2w5-ai-20261125)

**Status: FIXED (single-file lane) — pending executable qualification.**

`src/app/test_runner_new/test_runner_single.spl` now has a dedicated
all-examples-skipped verdict branch, placed after the BLOCKED branch and
ahead of the structured-evidence / `--assert-ran` / zero-executed branches.
When every declared example was deliberately skipped (`skip_if` / `skip` /
`return "skip: ..."` — the `... skipped (reason)` / `○ ... (skipped)`
markers `count_real_skips()` already recognises), nothing executed, nothing
failed, the child exited 0, output was not truncated, and any child verdict
line is clean (executed=0, failed=0, dropped=0), the file now gets:

- exit code 0 (non-failing, per the unblock condition above),
- `SPEC FILE VERDICT: <path> outcome=NOT_RUN ... skipped=N
  reason=all-examples-skipped` (same outcome token as the
  platform-os-mismatch skip precedent), and
- a `SKIPPED <path> (all examples skipped)` tail instead of `PASS`.

Deliberately unchanged:

- A `pending()`-only file still fails closed — `... pending` markers are not
  skip markers; an unimplemented example is an authoring gap, not deferral.
- A file that ran nothing WITHOUT skip markers still fails
  `reason=zero-examples`, including under `--assert-ran`.
- Any run carrying real failure evidence (nonzero exit, truncation, failed
  summary/verdict, dropped examples) never reaches the new branch.
- The directory/daemon lane (`test_runner_main` / `test_daemon`) is out of
  scope for this fix; the reported repro is the single-file lane.

Contract coverage: new fixture
`test/fixtures/test_runner_single/all_skipped_spec.spl` (single always-skipped
example, the board-Vulkan shape) and a new case in
`test/01_unit/app/test_runner_new/single_structured_evidence_precedence_spec.spl`
asserting exit 0, `reason=all-examples-skipped`, and no `no examples
executed` line. The pre-existing `zero_examples_spec.spl` fail-closed case is
untouched (it prints no skip markers).

Verification limit: executable runs are environment-blocked on this host —
release/1.0.0 HEAD is source/binary inconsistent (cfd89933699's
`@representation_boundary` annotations are rejected by the pinned Rust seed
v1.0.0-rc.1), so `bin/simple.exe test` and even `bin/simple.exe lint` fail
before reaching any runner code. Verified by code inspection: branch order,
guard conjuncts, verdict-line field compatibility, summary/exit-code flow,
and the untouched fail-closed paths. Run the new contract case on a Stage 4
self-hosted CLI to close qualification.
