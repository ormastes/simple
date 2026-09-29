# FreeBSD QEMU full bootstrap fails closed at bootstrap reason-receipt policy

Date: 2026-09-25
Lane: `scripts/check/check-freebsd-bootstrap-qemu.shs --full`
Host: aarch64 Linux (KVM host; guest run as `QEMU_ARCH=amd64` under TCG —
only the amd64 base image is admitted locally).

## Symptom

`--full` progresses through VM boot, deps install, and project sync, then the
in-guest canonical bootstrap stops before any stage starts:

```
bootstrap-policy-error: reason-receipt-required; run 'simple run src/app/build/bootstrap_receipt_main.spl --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path> --parent-compiler-sha256=<hex64> --runtime-snapshot-sha256=<hex64> --planner-source-closure-sha256=<hex64> --planner-sha256=<hex64>'
```

(exit 64 from `scripts/bootstrap/bootstrap-from-scratch.sh`), after which the
wrapper's guest-log retrieval fails closed with
`rsync: change_dir "/root/simple/build/bootstrap/logs" failed` — the bootstrap
never created `build/bootstrap/logs`.

## Root cause chain (two independent defects)

1. **Guest sync excluded the canonical kernel policy authority** — FIXED in
   `93bdb922069`. The guest rsync had `--exclude='/doc/'`, but
   `bootstrap-from-scratch.sh` reads
   `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn` as the
   canonical kernel policy authority and fails closed when absent. First
   failure observed (2026-09-25): `canonical kernel policy authority is
   missing`. Fix re-includes only that file via an ordered rsync filter chain
   (`--include` for `/doc/` … `plugin_arch/kernel_closure.sdn`, then
   `--exclude='/doc/**'`; note `--exclude='/doc/*'` is NOT sufficient — `*`
   does not cross `/`, so everything under the included dirs leaked through
   the default-include fallthrough).

2. **The check never wires a bootstrap reason receipt** — OPEN. The check
   invokes (in-guest, as root):

   ```
   sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --mode=dynload --no-mcp --jobs=2
   ```

   Since the admission-v2 policy (see
   `doc/08_tracking/bug/bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17.md`),
   full bootstrap without `--stop-after-stage2` requires a verified planner
   admission receipt (target `//bootstrap:stage4`). The only receipt-free
   paths are the stage-2 trust-root lanes (`--full-bootstrap
   --stop-after-stage2`, or a previously admitted
   `SIMPLE_BUILD_COMPILER` parent via `admit-stage2-parent.shs`). The wrapper
   has no `--bootstrap-receipt` argument, no receipt-producer step, and no
   env override, so `--full` cannot pass as written.

## Sanctioned remediation sketch (design-level, needs its own plan)

Staged in-guest flow inside the wrapper's `--full` mode:

1. Trust-root stage 2 in-guest: `bootstrap-from-scratch.sh --full-bootstrap
   --stop-after-stage2 --mode=dynload` (receipt-free by design; admits the
   stage-2 parent with runtime provenance).
2. Produce the admission in-guest with the admitted parent:
   `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs
   --target=//bootstrap:stage4 --reason=<typed> --parent-compiler=<admitted
   stage2>` (canonical producer; verifies parent authority, hashes parent /
   runtime snapshot / planner source+closure / git state, emits the 29-field
   receipt).
3. Continue: `bootstrap-from-scratch.sh --full-bootstrap --mode=dynload
   --no-mcp --jobs=2 --bootstrap-receipt=<receipt>`.

Constraints to design around: `QEMU_FULL_TIMEOUT` (default 7200s) must cover
all three phases under TCG (Rust seed rebuild + stage 2 in-guest is the long
pole); the receipt binds output roots under `<repo>/build` unless
`SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT` is set; `--validate-bootstrap-receipt`
exists for a cheap pre-flight of steps 2→3.

## Evidence

- Fixed-defect run log: `build/freebsd/vm/` wrapper output, 2026-09-25
  (`canonical kernel policy authority is missing`).
- Open-defect run log: same wrapper, post-fix, 2026-09-25
  (`reason-receipt-required`, then guest-log rsync failure).
- `--smoke` mode unaffected and PASS (does not enter the bootstrap).
