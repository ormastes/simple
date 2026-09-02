# Every Stage-3 attempt clobbers `admission.env`, breaking the NEXT receipt producer

**Status:** OPEN
**Filed:** 2026-09-02
**Severity:** P1 — costs a full trust-root Stage-2 rebuild (~20-40 min) per occurrence, and
misdirects the operator into believing the Stage-2 build is stale when it is not.

## Symptom

`produce-bootstrap-planner-admission-v2.shs` fails with:

    bootstrap-admission-error: parent-stage2-sanity-admission-mismatch

The obvious reading — "Stage 2 is stale, rebuild it" — is WRONG, and acting on it
wastes a full trust-root rebuild. This session did that three times before diagnosing it.

## The failing check

`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:126-128`:

```sh
admission_sha=$(bootstrap_planner_v2_hash_file "$admission_file")
[ "$(parent_field "$sanity_file" admission_receipt_sha256 || true)" = "$admission_sha" ] \
  || adm_fail parent-stage2-sanity-admission-mismatch
```

It compares the `admission_receipt_sha256` field recorded inside `stage2-sanity.receipt`
against a LIVE `sha256sum` of the file that receipt's own `admission_receipt_path` names —
`build/bootstrap/stage3/<triple>/stage2-admitted/admission.env`.

## Measured instance

| value | sha256 | mtime |
|---|---|---|
| recorded in `stage2-sanity.receipt` | `c5e85f8d7287f895…` | 16:58 |
| live `admission.env` | `82702b241f0ed13c…` | 17:02 |

The parent binary was NOT stale: receipt `candidate_sha256=565514d3bfab…` matched a live
hash of `stage2/<triple>/simple` exactly. The receipt was NOT half-written: all 5 fields
present, and it is written `tmp.$$` + `mv -f` (`bootstrap-from-scratch.sh:2869-2890`).

## Root cause

A Stage-3 attempt `rm -rf`s `stage2-admitted/` and republishes `admission.env`
(`bootstrap-from-scratch.sh:2296-2297, 2851`) but does NOT rewrite the parent receipts.
Parent receipts are rewritten ONLY in the `bootstrap_stage2_trust_root -eq 1` branch
(`:463-472`) — i.e. `--full-bootstrap --stop-after-stage2` with no receipt.

So **every Stage-3 attempt invalidates the producer for the next one**, whether or not
that attempt succeeds. In the measured case the attempt (pid 61227, 16:58:39) was itself
SIGTERM'd at 17:11:36 (`milestone=exit-143`), having already done the clobber.

## Why the operator is misled

The error names `stage2-sanity`, which points at Stage 2. But Stage 2 is fine — the
mutated file is a Stage-3 artifact. Nothing in the message says `admission.env` was
republished, or by what.

## Workaround (verified)

A receipt produced BEFORE the clobber still verifies, because
`bootstrap_planner_v2_verify` re-hashes 10 pinned artifacts and `admission.env` is not
among them. Measured today: `bootstrap_planner_v2_verify r3.receipt s3-wt` -> `rc=0`.
So reuse the surviving receipt via `--bootstrap-receipt=<path>` instead of rebuilding.

If a genuinely fresh receipt is needed, order it strictly:
**trust-root refresh -> produce receipt -> Stage 3**, because any Stage-3 attempt in
between re-clobbers.

## Suggested fixes (not implemented)

1. Have the Stage-3 republish path update `admission_receipt_sha256` in the parent
   receipts, or
2. drop `admission.env` from the comparison if it is not load-bearing for admission
   (the verifier already excludes it from its 10 pinned artifacts, which is evidence it
   may not be), or
3. at minimum, make the error message name the mutated file and say which stage rewrote
   it, so the operator does not rebuild Stage 2 for nothing.

## Scope note — RESOLVED 2026-09-02

The "only the trust-root branch writes parent receipts" claim was initially filed with a
caveat: a `src/`-wide grep had not completed on this starved host. That grep has since
finished. **`stage2-sanity.receipt` appears in exactly six `scripts/` files and has ZERO
hits under `src/`** — no Simple-side code writes or refreshes it. The sole writer is
confirmed to be the trust-root branch of `bootstrap-from-scratch.sh:2864-2890`.

(The workaround above never depended on this claim, but the claim is now established
rather than assumed.)
