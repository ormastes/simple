# Site 20: Stage 3 unreachable — the receipt chain has no entry point from a rust-seed Stage 2 (macOS, 2026-09-13)

- Status: OPEN (2026-09-13) — **instance of an already-OPEN root defect**, `bootstrap_admission_v2_circular_and_cannot_express_imported_parent_2026-08-18.md` ("nothing in the repo ever WRITES the two receipts the gate reads"). Kept for the macOS run-35 evidence; the root defect is tracked there, not here.
- Area: bootstrap Stage 2 -> Stage 3 handoff; planner admission v2 receipt chain
- Found by: macOS lane F73 run 35, worktree `agent-a73a6f3780a2bd75b`, tip
  `60c78b96789` (carries PR #903, the site-19 fix)
- Blocks: Stage 3, the full CLI, and Stage 4. Stage 2 itself is ADMITTED.

## What happened

Run 35 is the first macOS run to get a Stage 2 ADMITTED (site 19 cleared):

```
Stage 2 admitted; stopping before Stage 3 as requested.
```

Both documented routes to Stage 3 then fail identically, rc=64:

```
bootstrap-policy-error: reason-receipt-required; run 'simple run src/app/build/bootstrap_receipt_main.spl --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path> --parent-compiler-sha256=<hex64> --runtime-snapshot-sha256=<hex64> --planner-source-closure-sha256=<hex64> --planner-sha256=<hex64>'
```

- `--resume-stage3-from-admitted=<output>` (the prescribed route)
- a plain continuous `--full-bootstrap --mode=dynload --jobs=half` run, which
  reuses the admitted Stage 2 and hits the same gate within seconds

## The chain, and where it has no entry point

Stage 3 needs a planner receipt. The canonical producer for it is
`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`, which derives
every hash itself but first verifies the PARENT authority. Walked through with
the real artifacts:

1. `--bootstrap-output` under centralized storage is refused as
   `bootstrap-output-outside-allowlisted-root` unless
   `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT` names the storage root (the
   allowlist is `<repo>/build/**` or that env root —
   `scripts/check/lib/bootstrap-stage3/authority.shs:619`). Surmountable.
2. The parent must be `<output>/stage2/<triple>/simple`, not
   `stage3/<triple>/stage2-admitted/simple` (`parent-compiler-not-under-build-bootstrap-stage2`).
   Both are byte-identical here (`aed71b28…`). Surmountable.
3. It then requires a Stage-2 ADMISSION receipt with
   `schema=simple-bootstrap-stage2-admission-v2 status=admitted`, plus a
   provenance receipt whose `admission_receipt_sha256` matches
   (`parent-stage2-admission-invalid`). **Neither file exists**, and the Stage 2
   run says why, in its own verdict:

```
PASS — 2 invariant(s) checked (producer identified, skip recorded),
producer=rust-seed cannot publish the manifest; Stage 3 reuse disabled;
evidence=.../stage3/aarch64-apple-darwin/phase2-compatibility.manifest.not-published
```

`scripts/bootstrap/publish-stage2-parent-receipts.shs` is the publisher for
those receipts, but it CONSUMES an existing admission receipt (it re-verifies
`schema`/`status`/paths/hashes out of it) rather than minting one. So on a lane
whose only trust root is the Rust seed — which is exactly what `--full-bootstrap`
is for — the chain closes on itself: Stage 3 needs a planner receipt, which needs
a Stage-2 admission receipt, which only a non-seed producer can publish, which
requires a Stage 3 that has already run.

## What was NOT done, deliberately

No receipt was manufactured. Hand-writing the admission/provenance pair, or
pointing the producer at a binary that did not produce them, would defeat the
non-circular trust model these gates exist to enforce — the same reasoning as
`doc/09_report/macos_arm64_stage2_stage3_producer_attempt_2026-09-03.md`, which
reached this conclusion from the opposite direction (a no-seed lane). That report
assumed a seed-authorized run would resolve it; run 35 shows it does not, because
the seed producer is refused publication rights.

## Evidence

- admitted Stage 2: `<storage>/build/bootstrap/stage2/aarch64-apple-darwin/simple`,
  139,504,568 B, sha256 `aed71b284fd897f6dff37ee2cda23056a32b4967c54d99468fea6aa8fc07124a`
- `stage2-sanity.env`: `status=pass ... checks_run=5`
- `stage2-receiver.env`: `status=pass probe_exit=0` (the site-19 probe)
- `phase2-compatibility.manifest.not-published`

## Next action (owner decision, not a local fix)

Either grant the `explicit-full-bootstrap-stage2-trust-root` authority a way to
MINT the Stage-2 admission + provenance pair (the authority string is already
accepted by `publish-stage2-parent-receipts.shs`, so the concept exists — what is
missing is the producer), or document a supported bootstrap-from-seed lane that
reaches Stage 3 without one. Until then macOS stops at an admitted Stage 2.

## Correction (2026-09-13, same day): this is not a new defect

`bootstrap_admission_v2_circular_and_cannot_express_imported_parent_2026-08-18.md`
already records the root cause, OPEN since 2026-08-18, in its own words:

> receipt needs stage2, stage2 needs a bootstrap run, the bootstrap run needs
> the receipt. A tree that has never bootstrapped cannot bootstrap.
> ... Nothing in the repo ever WRITES the two receipts the gate reads.

Run 35 adds two things that record does not have, and nothing else:

1. **It is reached from a SUCCESSFULLY admitted Stage 2, not a fresh tree.** The
   08-18 record's cycle is stated for a tree with no `build/bootstrap/stage2/`.
   Here Stage 2 exists, is admitted, and is byte-stable — and the chain still has
   no entry, because the missing artifacts are the admission/provenance receipts,
   which no producer writes, rather than the compiler.
2. **A third route is refused, including the Stage-4 entry point.** Measured:

   | route | rc |
   |---|---|
   | `bootstrap-from-scratch.sh --resume-stage3-from-admitted=<output>` | 64 |
   | `bootstrap-from-scratch.sh --full-bootstrap --mode=dynload --jobs=half` | 64 |
   | `bootstrap-strategy.sh -- --full-bootstrap --mode=dynload --jobs=half` (with `SIMPLE_BOOTSTRAP_STAGE4_QUARANTINE=1`) | 64 |

   all with the identical `bootstrap-policy-error: reason-receipt-required`.
   `bootstrap-strategy.sh` is a supervisor, not a producer — its own header says
   "The existing engine remains the only producer/admission authority", and with
   no `--bootstrap-receipt=` it `exec`s the engine unchanged (lines 92-98). So
   the Stage-4 path is gated by the same missing receipt, not by a separate one.

## Wording correction

An earlier draft of this record said the Stage 2 verdict "states outright" that
the seed producer may not publish. It over-read the line. `producer=rust-seed
cannot publish the manifest; Stage 3 reuse disabled` is about the
`phase2-compatibility.manifest`, which gates REUSING a prior Stage 3 output — it
is context, not proof. The evidence for this record is the measured rc=64 on all
three routes above.
