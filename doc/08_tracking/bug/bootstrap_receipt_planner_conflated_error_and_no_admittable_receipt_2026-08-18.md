# bootstrap receipt planner conflated two causes; and no admittable receipt can be produced on this tree (2026-08-18)

Status: PARTIALLY FIXED (message defect fixed) / OPEN (P1 — admission still unsatisfiable here)

## Symptom

    bin/simple run src/app/build/bootstrap_receipt_main.spl \
        --bootstrap-reason=self-host-convergence-check --bootstrap-receipt=<path>
    bootstrap-policy-error: receipt-write-failed: <path>   RC=2

Reported for both an absolute path under /mnt/data/tmp and a relative path
inside the repo, in directories that exist and are writable.

## Measured root cause (defect 1 — conflated message)

`src/app/build/bootstrap_receipt_planner.spl:60` read

    if receipt.len() == 0 or not file_write(receipt_path, receipt + "\n"):
        print("bootstrap-policy-error: receipt-write-failed: " + receipt_path)

One message for two causes. Measurement, same directory, only the four
admission hashes added (64 lowercase hex each):

| run | result |
|---|---|
| no `--*-sha256=` flags | `receipt-write-failed`, RC=2, no file |
| all four sha flags supplied | `bootstrap-plan: execution=not-attempted ...`, RC=0, **454-byte receipt written** |

So `file_write` was never the failure. `bootstrap_authorization_receipt_v2`
(`src/app/build/targets/bootstrap_policy.spl:55-63`) returns `""` when any of
`parent_sha256` / `runtime_sha256` / `source_closure_sha256` / `planner_sha256`
is not canonical 64-hex — empty counts as not canonical — and the empty receipt
was reported as a write failure.

**Fix applied** (`bootstrap_receipt_planner.spl`): three distinct messages —
`admission-hash-required: <flag>=<64 lowercase hex>` naming the FIRST missing
field, `reason-not-allowed-for-target: target=... reason=...`, and
`receipt-write-failed: <path>` now meaning only a real write failure. Verified:
the no-flags run now prints
`bootstrap-policy-error: admission-hash-required: --parent-compiler-sha256=<64 lowercase hex>`.

## Defect 2 (OPEN) — the authorization leaf is not the receipt the gate wants

`bootstrap-from-scratch.sh:301` `--bootstrap-receipt=` expects the **29-field
planner admission v2** record, not the single-line authorization leaf the
planner emits. Measured with a valid leaf:

    sh scripts/bootstrap/bootstrap-from-scratch.sh --validate-bootstrap-receipt \
        --bootstrap-receipt=build/bootstrap/receipt_probe/probe.receipt
    bootstrap-policy-error: planner-admission-v2-unbound
    bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2   RC=64

The only producer is `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`,
which requires an admitted Stage 2 parent under `$root/build/bootstrap/stage2/`
with `stage2-sanity.receipt` + `stage2-provenance.receipt`. This tree has no
`build/bootstrap/stage2/` at all:

    bootstrap-admission-error: parent-compiler-missing-or-not-canonical

**Consequence: on this machine no receipt can be produced, therefore no
bootstrap can start.** The admission chain is circular for a tree with no
stage2: admission needs an admitted stage2 parent, stage2 comes only from a
bootstrap, and the bootstrap needs admission. This is the honest residual
already acknowledged at the bottom of
`bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17.md`;
this row records that it is now the ACTIVE blocker, not a footnote.

**Needed (owner decision, not taken here — it is a security-model change):** a
genesis path that admits a first stage2 from the Rust seed with recorded,
distinguishable provenance, or an out-of-band import of an already-admitted
stage2 tree.

## Defect 3 (OPEN, minor) — `simple build bootstrap` is not a planner

`bin/simple build bootstrap --bootstrap-reason=... --bootstrap-receipt=...`
accepts both flags and then starts a real Stage 1 (observed dying on
`native-build worker timed out after 180s`) instead of planning. The error text
at `bootstrap-from-scratch.sh:302` tells users to run exactly that command, so
the advice is wrong on both counts.

## Not done
No bootstrap was started; no binary was rebuilt or redeployed.

## Triage 2026-11-10 (p3-boot2 lane)

SUPERSEDED — all three defects are fixed on work/p3-boot2-20261110 (base
origin/release/1.0.0). One verification cycle; the doc's original reproducer
was re-run live with this lane's seed binary.

Defect 1 (conflated message) — verified live:
`SIMPLE_LIB=src bin/simple.exe run src/app/build/bootstrap_receipt_main.spl
--bootstrap-reason=self-host-convergence-check
--bootstrap-receipt=/tmp/p3boot2-receipt-probe.receipt` prints exactly
`bootstrap-policy-error: admission-hash-required:
--parent-compiler-sha256=<64 lowercase hex>` and exits 2, and writes NO file
(the probe path stays absent — `receipt-write-failed` no longer masks a
missing-hash refusal). The three distinct messages sit at
`src/app/build/bootstrap_receipt_planner.spl:74` (`admission-hash-required`),
`:84` (`reason-not-allowed-for-target`), `:95` (`receipt-write-failed`,
real write failures only).

Defect 3 (`simple build bootstrap` is not a planner) — fixed both halves:
- CLI: `src/app/build/cli_entry.spl:181-182` routes `build bootstrap` to
  `plan_bootstrap_authorization` ("Emit authorization only; this function
  never starts a bootstrap stage"), with the explicit comment at :211-213
  that bootstrap never falls through to native-build; help text :158
  describes it as the receipt planner.
- Script advice: `scripts/bootstrap/bootstrap-from-scratch.sh:787-791` now
  names the planner command `simple run src/app/build/bootstrap_receipt_main.spl
  --bootstrap-reason=... --bootstrap-receipt=... <four admission hashes>`,
  replacing the old `simple build bootstrap` wording (comment at :784-788
  records why), gated by
  `scripts/check/check-bootstrap-receipt-instruction.shs`.

Defect 2 (no admittable receipt on a tree with no stage2 — circular
admission) — superseded by the implemented genesis path (the owner
security-model decision this doc said was needed):
`scripts/bootstrap/bootstrap-from-scratch.sh:757-765` gives
`--full-bootstrap --stop-after-stage2` (no receipt) a narrow trust-root
lane with recorded, distinguishable provenance
`explicit-full-bootstrap-stage2-trust-root` (plus `--stop-after-seed`'s
`explicit-full-bootstrap-seed-prerequisite`), and :767-776 lets a previously
admitted pure-Simple parent (`SIMPLE_BUILD_COMPILER`, provenance-bound via
`scripts/bootstrap/admit-stage2-parent.shs`) refresh the first Stage-2
producer. The canonical producer allow-lists both authorities
(`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:172-173`),
and `scripts/check/check-bootstrap-planner-admission-producer.shs:295`
pins the trust-root authority. The fail-closed receipt validation itself was
verified end-to-end in the p3-boot batch-1 lane (sibling record
`bootstrap_admission_v2_circular_and_cannot_express_imported_parent_2026-08-18`).
