# Windows Phase 3 blocked: planner-admission-v2 producer refuses any bootstrap output outside `<repo>/build/`

**Date:** 2026-09-02
**Status:** OPEN — blocks W2 (Phase 3) on the Windows MSVC lane
**Failing acceptance gate:** §8 *Provenance* / *Phase 3* of
`doc/03_plan/compiler/windows_bootstrap_separate_hosts_nonconflicting_plan_2026-08-30.md`

## Ground truth this was measured against

Windows MSVC **Stage 2 is admitted** and its receipt is on disk:

```
/d/simple_build/bootstrap-msvc/stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env
  schema=simple-bootstrap-stage2-admission-v2
  status=admitted
  candidate_sha256=4a8dd3eb3887b9cb61608dd6cc668dafa18bbd75bd0d98326328df48c6d54db5
  admission_identity=a2eedf0d7d8c2fd955f9726eea77e4535f89bd00645882792a13a45ed12884d4
  checks_executed_at_admission=1
  checks_replayed_during_stage3=0
```

Candidate `stage2-admitted/simple.exe`, 108,423,680 B, re-hashed 2026-09-02:
`sha256=4a8dd3eb...d54db5` (matches), `md5=438f4adb7e9cda4aa2b4b272b5695743`.
`stage2/x86_64-pc-windows-msvc/stage2-sanity.receipt` and `stage2-provenance.receipt`
both exist. **No Stage 3 artifact exists** — `stage3-home/` and `stage3-tmp/` are empty.

## The blocker

**Every** Stage 3 entry lane in `scripts/bootstrap/bootstrap-from-scratch.sh`
is gated on a planner-admission-v2 receipt targeting `//bootstrap:stage3`
(lines 411-448). Measured 2026-09-02, all three produce the identical typed refusal:

| probe | command | result |
|---|---|---|
| P2 | `bootstrap-from-scratch.sh --resume-stage3-from-admitted=/d/simple_build/bootstrap-msvc` | `bootstrap-policy-error: reason-receipt-required` |
| P3 | `bootstrap-from-scratch.sh --resume-stage3-from-admitted=build/bootstrap` | `bootstrap-policy-error: reason-receipt-required` |
| P4 | `bootstrap-from-scratch.sh --output=/d/simple_build/bootstrap-msvc --stop-after-stage3 --mode=dynload` | `bootstrap-policy-error: reason-receipt-required` |

The **only** producer of that receipt is
`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`.
(`src/app/build/bootstrap_receipt_main.spl` mints only the 6-field
*authorization* text — one field of the 29-field receipt. Verified: grepping
`src/app/build/` and `src/app/cli/bootstrap_reason_planner.spl` for
`simple-bootstrap-planner-admission-v2`, `planner_smoke_path`, and
`cache_scope_key` returns **zero** hits, so no `.spl` path emits a v2 receipt.)
It refuses:

```
$ sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
    --target=//bootstrap:stage3 --reason=verify-landed-compiler-fix \
    --bootstrap-output=/d/simple_build/bootstrap-msvc \
    --parent-compiler=/d/simple_build/bootstrap-msvc/stage2/x86_64-pc-windows-msvc/simple.exe
bootstrap-admission-error: bootstrap-output-outside-build-root
```

Two independent hardcodings of the canonical repo build root, both in that file:

- line 86 — `case "$adm_bootstrap_output" in "$adm_root"/build/*) ;; *) adm_fail bootstrap-output-outside-build-root ;; esac`
- admission-file residency — `case "$admission_file" in "$adm_root/build/bootstrap"/*) ;; *) adm_fail parent-stage2-admission-outside-bootstrap ;; esac`
  This second one ignores `--bootstrap-output` entirely, so relaxing the first
  alone would not be enough.

This **contradicts the plan's own topology**: §3 and W2 mandate *private,
per-lane* bootstrap outputs, and the Windows lane builds on `D:` (host
disk-space and antivirus constraints). §7/§8 never schedule receipt production
at all — grepping the plan doc for `REASON_RECEIPT|planner admission|bootstrap-receipt`
returns **zero** hits.

## Why this was NOT worked around

Every available workaround is provenance fabrication or a spec violation, and
§8 (*Security: no stubs/fallback*) forbids both:

- **Relaxing either check.** The gate is fail-closed by design
  (`check-bootstrap-planner-admission-producer.shs` header: *"Weakening the
  guard was never the fix"*), and it would change Unix behaviour, against the
  standing constraint.
- **NTFS junction / MSYS `fstab` mount / copying the receipts under
  `build/bootstrap/`.** All make a receipt record a path other than physical
  truth. Copying additionally cannot work: `stage2-sanity.receipt` records
  `admission_receipt_path` as the `D:` location, and editing receipts is out.
- **Re-running with an in-repo private lane, e.g. `--output=build/bootstrap-msvc`.**
  This does **not** satisfy the producer either. Check 1 (`$adm_root/build/*`)
  would pass, but check 2 hardcodes `"$adm_root/build/bootstrap"/*` for the
  admission file, and such a lane puts its `admission.env` under
  `build/bootstrap-msvc/stage3/...`, which does not match. **The only output
  directory satisfying both checks is literally `<repo>/build/bootstrap`** — the
  canonical *shared* dir, which collides with §6 nonconflicting ownership (other
  sessions write it) *and* would still rebuild Stage 2 from today's drifted tree,
  producing a *different* Phase 2 than the pinned admitted one. W2 requires
  "only the admitted Phase 2". So even a private in-repo lane cannot mint a
  receipt: the constraint is not "inside the repo", it is "the one shared lane".

## Second, independent blocker (Unix-only recovery lane)

`scripts/bootstrap/resume-stage3-from-admitted.sh` — the lane whose stated
purpose is exactly W2 — is unusable on Windows for three further reasons:

1. Line 15 rejects any absolute or non-repo-relative `OUTPUT_DIR`; the Windows
   lane output is `/d/simple_build/bootstrap-msvc`.
2. **Zero Windows awareness.** `grep -n 'exe_suffix|\.exe|\.lib|msvc|windows'`
   over the file returns **0 lines**. It hardcodes
   `stage2-admitted/simple` (Windows: `simple.exe`) and
   `libsimple_native_all.a` / `libsimple_compiler_backfill.a`
   (Windows/MSVC: `simple_native_all.lib` / `simple_compiler_backfill.lib`).
   Compare `bootstrap-from-scratch.sh:870-877`, which does carry `exe_suffix`.
3. `bootstrap-from-scratch.sh:509` pins it to `--jobs=1`, against the measured
   Windows profile (`Native build jobs: 24 / self-host jobs: 24`).

Note also `bootstrap-from-scratch.sh:387`: `--stop-after-stage3` and
`--resume-stage3-from-admitted` are **mutually exclusive**; passing both is a
usage error, and the bare (value-less) `--resume-stage3-from-admitted` prints help.

## Pre-existing defect found and fixed here

`scripts/check/check-bootstrap-planner-admission-producer.shs:26` set
`producer="$root/scripts/bootstrap/bootstrap-from-scratch.sh"` — the **wrong
file**. Its first assertion requires both `--entry-closure` and
`--entry "$planner_source"` to be present in `$producer`; measured counts:

| file | `--entry-closure` | `--entry "$planner_source"` |
|---|---|---|
| `bootstrap-from-scratch.sh` | 8 | **0** |
| `produce-bootstrap-planner-admission-v2.shs` | 2 | **1** |

So the gate inspected a file that can never satisfy it and was **permanently**
`FAIL — producer does not constrain the planner build to its entry closure` —
the exact denial-of-service failure mode its own header warns against.
Repointed at the real producer. **Cross-platform impact: none** — it is a text
grep over repo files, identical on every OS, and the gate is red before and
after, so no verdict flips. It is not wired into any push-tier row of
`config/check/must_check_gates.sdn`.

It now advances past that assertion and fails deeper, at
`FAIL — could not create fixture Stage-2 admission`
(`check-bootstrap-planner-admission-producer.shs:146-151` calling
`bootstrap_stage3_write_stage2_admission_receipt`,
`scripts/check/lib/bootstrap-stage3/sanity.shs:244`): drift between the
fixture's synthesized `stage2-sanity.env` field set and what
`bootstrap_stage3_verify_sanity_evidence_receipt` requires. Platform-
independent, pre-existing, **not** fixed here.

## Unblock condition (either is sufficient)

1. **Preferred.** Give the producer a first-class private-lane mode: bind the
   admission-chain residency check to the *declared* `--bootstrap-output`
   (verified canonical and hash-pinned) instead of the literal `$adm_root/build`,
   and apply it to the `admission_file` check too. This needs the owner of the
   admission schema to sign off — it is a provenance control, not a path
   convenience.
2. Port `resume-stage3-from-admitted.sh` to Windows (`exe_suffix`, MSVC lib
   names, non-repo-relative output, honour `SIMPLE_NATIVE_BUILD_THREADS`).
   This still needs (1), since it also demands the `//bootstrap:stage3` receipt.

Until then, **Windows Phase 3 cannot be attempted honestly.** No Stage 3
receipt exists and none is claimed.
