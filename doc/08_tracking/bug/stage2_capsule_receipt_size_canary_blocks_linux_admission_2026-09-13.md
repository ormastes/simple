# Stage-2 admission is now blocked on Linux aarch64 by the capsule-receipt size canary — the `FileFingerprint.size` miscompile is live here too

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-5, `work/bootstrap-full-3-2026-09-12`
- Severity: **blocks Stage-2 admission on Linux aarch64**, the same way it
  already blocks macOS. It is the CURRENT blocker on this platform, replacing
  `bootstrap_mode_assumes_bootstrap_cli_probe_chain_2026-09-13.md` (site 3),
  which is fixed and measurably gone.
- Underlying codegen defect already recorded:
  `bootstrap_stage2_native_capsule_receipt_mismatch_equal_byte_counts_2026-09-12.md`
  and `stage2_sanity_native_capsule_receipt_content_mismatch_2026-09-13.md`
  (macOS). This record adds the Linux evidence and the admission consequence.

## Verdict, verbatim

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 0)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
[native-compile-failed] scripts.check.cert.redeploy_gate.fixtures.hello_world:
  AOT compile error in ...hello_world:
  capsule-receipt-size-implausible:field=310824753:runtime=1080:.../object.....o
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stage 2 itself **built and linked clean**; the failure is entirely inside the
smoke build the candidate performs.

## Measured

New Stage-2 binary: `build/bootstrap-boot5/stage2/aarch64-unknown-linux-gnu/simple.rejected`,
sha256 `69fdfbf8b1c5e152...`. The object is 1080 bytes every time. The
struct-field read of that same size answered a **different wrong value in each
of three runs**:

| run | `SIMPLE_BOOTSTRAP` | `field=` | `runtime=` |
|---|---|---|---|
| sanity harness | 0 | 310824753 | 1080 |
| `disc5.sh bs0_trace` | 0 | 1063910161 | 1080 |
| `disc5.sh bs1_new` | 1 | 183238833 | 1080 |

Run-to-run variance on an unchanged binary and an unchanged input is the
signature of a garbage read, not of a wrong constant. It is **independent of
`SIMPLE_BOOTSTRAP`** — the identical failure occurs in both passes — so it is
unrelated to the bootstrap-mode routing fixed in this lane.

## Why no previous lane saw it

The gate landed in `eb458611bcd` ("restore the capsule-receipt size fix PR #702
clobbered, and gate line 4", 2026-09-13). BOOT-4's Stage-2 binaries were
produced by `resume-stage2-from-cache.sh`, which clones the content-addressed
native cache, so the object for `driver_aot_native_output.spl` was reused from
an earlier compile. Measured directly on the two binaries:

    strings simple.rejected(BOOT-4, 79139f420ee07450) | grep -c receipt-size-implausible  -> 0
    strings simple.rejected(BOOT-5, 69fdfbf8b1c5e152) | grep -c receipt-size-implausible  -> 2

**BOOT-4's `SIMPLE_BOOTSTRAP=0` PASS was obtained on a compiler that did not
contain this gate.** A cache-cloned Stage 2 can lag the source tree, and a green
sanity verdict from one is not evidence about code that was never compiled in.
That is worth its own attention independently of this defect.

## What is actually wrong

`driver_native_capsule_receipt_size_reason_v1`
(`driver_aot_native_output.spl:222-246`) fails the build on

    if field_size != runtime_size:
        return "receipt-size-implausible:field={field_size}:runtime={runtime_size}"

`field_size` is `FileFingerprint.size` read off an optional-bound struct — the
value the macOS lane already proved is miscompiled and deliberately routed
AROUND. `runtime_size` comes from `rt_file_size` and is the value actually
written into the receipt. So the receipt content is correct; the build fails
purely because the canary observed the known defect.

That is the canary's stated intent ("turns a silent hazard into a build failure
at the site that noticed it"). The consequence, now measured, is that Stage-2
admission cannot succeed on ANY platform where the scalar-field miscompile is
live — which is now both macOS and Linux aarch64.

**Not relaxed here, deliberately.** Making the canary advisory would disable a
fail-closed gate another lane installed on purpose, and this lane has no mandate
to do that. The fix belongs at the codegen defect (an `i64` struct field read
through an optional binding returning a tagged pointer), not at the detector.

## Reproduction (about 15 seconds, no bootstrap needed)

    CAND_OVERRIDE=/home/yoon/dev/simple-boot5/build/bootstrap-boot5/stage2/aarch64-unknown-linux-gnu/simple.rejected \
      sh scratchpad/boot5/disc5.sh bs0_trace
    grep 'capsule-receipt-size-implausible' scratchpad/boot5/d_bs0_trace.log
