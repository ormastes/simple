# bootstrap receipt planner conflated two causes; and no admittable receipt can be produced on this tree (2026-08-18)

Status: PARTIALLY FIXED (message defect fixed) / OPEN (P1 — admission still unsatisfiable here)

### Defect 1 re-verified CLOSED 2026-09-02 (`origin/main` @ `1b76db1d6c3`)

The conflated message is gone. `src/app/build/bootstrap_receipt_planner.spl`
now splits the two causes into two distinct, separately-reachable diagnostics:

```
:80-83   if receipt.len() == 0:
             print("bootstrap-policy-error: reason-not-allowed-for-target: target=" +
                 bootstrap_target + " reason=" + reason_name)
             return 2
:84-86   if not file_write(receipt_path, receipt + "\n"):
             print("bootstrap-policy-error: receipt-write-failed: " + receipt_path)
             return 2
```

`receipt-write-failed` is now emitted only for a genuine write failure, so the
misdiagnosis this record documents (a policy rejection reported as a filesystem
problem) can no longer occur. The four admission-hash flags are also validated
up front with their own message (`admission-hash-required: <flag>`, `:72-77`),
which is what the original measurement was actually hitting.

**Defect 2 (no admittable receipt can be produced on this tree) remains OPEN**
— confirming it requires running a bootstrap, which was out of scope for this
pass.

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
