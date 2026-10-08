# Item5 QEMU application-runner preparation

This change adds an opt-in fixed-profile QEMU path to the item5 app receipt
runner. Native mode retains the existing v2 build-manifest contract, six-column
`runs.tsv`, and completion marker. QEMU mode requires the separate v3 manifest,
stages the target runtime and provenance inputs, and routes both the watchdog
and guest observer through one fixed-profile launcher. The manifest validator
continues to return exactly four provenance fields; the runner validates their
shapes before recording `app_source_tree_oid`.

The focused target-manifest test passed for all nine profile definitions,
derived bitmap loop totals, 15 rejection cases, and exact preservation of the
fourth provenance field through the runner-style tab-separated read. Existing
native manifest and runner preflight tests also passed. Those preflight checks
did not execute Simple apps.

The target PID probe compiled a small C `main` and the existing test observer
for AArch64 and RISC-V. It then used the same `item5-qemu-guest-exec.shs`
launcher intended for app runs. Each compile and guest execution was guarded by
the process-tree watchdog with a 1 GiB enforced RSS ceiling and 60-second
timeout. All nine fixed QEMU profiles emitted a valid no-load receipt whose
guest PID equaled the watchdog QEMU root PID:

| Profile family | Profiles | Result |
|---|---|---|
| AArch64 | NEON; SVE VQ1/2/4; SVE2-capable QEMU VQ1/2/4 | PID match and no-load receipt for all seven |
| RISC-V | RVV128; RVV256 | PID match and no-load receipt for both |

The retained terminal record is
`build/review/item5-qemu-pid-probe-20261008/profiles.tsv`. It records the nine
watchdog root PIDs and the QEMU executable hashes. QEMU was version 10.2.1 for
both targets; the cross compiler was LLVM clang 23.1.3. The observer DSO and
probe hashes are in the same build/review directory and were computed after
the run. The runner passes `LD_PRELOAD` only through QEMU's guest environment;
host preload/audit variables are cleared.

This proves only the runner's target process/observer identity path. It does
not prove Simple compiler target builds, provider admission, vector instruction
execution, DB or HTTP app behavior, SVE2-only instruction execution, target
performance, or default-image size. No Simple app binary was run. App build
provenance remains caller-supplied and is explicitly described that way by the
runner.

Scoped verification performed from WSL Ubuntu:

```text
bash -n run-item5-app-vector-receipts.shs item5-qemu-guest-exec.shs test-item5-qemu-target-manifest.shs test-item5-qemu-pid-profiles.shs — PASS
perl -c item5-app-build-manifest.pl — PASS
test-item5-qemu-target-manifest.shs — PASS profiles=9 derived_loops=9 rejected=15
test-item5-app-build-manifest.shs — PASS positive=1 rejected=8
test-item5-app-vector-receipt-runner.shs — PASS parser/staging preflight only; no app executed
test-item5-qemu-pid-profiles.shs — PASS profiles=9; simple_apps=not_run
```

Source hashes at this evidence checkpoint:

```text
run-item5-app-vector-receipts.shs 70d285ecd4d9caeb0c3274b3b3de25022f7e99222c1f41e3738d89bc66d4e1d9
item5-app-build-manifest.pl e31349b069da4e5f16c35070c360dc8f2ac7050af85674d7de02bba04ac1d2b3
Item5QemuProfile.pm b7db4cbb3843fedca7c2c240df4ba7244b20c3dc5dacf6bae772024702764b3d
item5-qemu-guest-exec.shs 42eadee24d36b9e9c3aa652374ea7917c2d9a6119b5b177423ee9d2fcedc4bde
test-item5-qemu-target-manifest.shs 6bf1aed9bd4cb305fe1d02d894c99328abd2d581cdb32512db944f39e1791884
test-item5-qemu-pid-profiles.shs 5bdd5fd1c0ecd1e67e0ca1fcf688dab7404ff92e9a42c3807af1332634f9cd55
item5-qemu-pid-probe.c 935e4b5dbcef9421a4cb02f4eb8a783ae983a982b5749580f6525d2a70cf179a
```
