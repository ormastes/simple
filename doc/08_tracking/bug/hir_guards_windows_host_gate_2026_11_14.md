# HIR hardening guards: runtime-backed checks are host-gated on Windows

Date: 2026-11-14
Branch observed: `release/1.0.0` @ `228560191e0`
Host: Windows (Git Bash), x86_64, `bin/simple` = Rust seed (no `bin/release/*/simple` yet)

## Symptom

On a Windows host without a self-hosted Simple binary, several
`scripts/check/check-hir-*.shs` guards fail in selftest with:

```
selftest: fresh fixture did not PASS: ERROR — nothing was checked
(regeneration failed: [engine-demotion] reason=hybrid-interp-splice
detail=rt_process_owned_v3_result_value,rt_process_observation_v4_reserved_confirm_release_value,...
```

Final verdict: `FAIL — selftest failed; the guard itself is broken` (rc=1).

Confirmed on `check-hir-visitors-fresh.shs` (2026-11-14, lane hir-batch).

## Root cause

`check-hir-visitors-fresh.shs:46` defaults

```sh
SIMPLE_BIN=${SIMPLE_BIN:-$REPO_ROOT/bin/release/x86_64-unknown-linux-gnu/simple}
```

i.e. the guard's reference runtime is the **Linux** self-hosted binary. On
Windows that path does not exist, so the guard silently falls back to
`$REPO_ROOT/bin/simple` (the Rust seed). The seed runs the fixture generator
in `hybrid-interp-splice` mode and demotes because the spliced workload
references runtime symbols that are not available to it on this host
(`rt_linux_group_*`, `rt_process_owned_v3_*`, ...). The selftest then
reports "guard itself is broken".

## Classification

NOT a product regression on `release/1.0.0`:

- Static/source-level hir guards run clean on the same host
  (`check-hir-expr-kind-exhaustive.shs` PASS, 24 matches;
  `check-hir-symbol-table-module-reset.shs` PASS, 9 invariants).
- Guards that default to `bin/simple` (the seed) and do not need the
  hybrid splice give real signal on this host.

Host support gap: the runtime-backed hir guards need a **self-hosted binary
for the host triple**. On Windows that binary only exists after a successful
stage-2/3 bootstrap — so these guards are effectively stage-3-runtime-gated
here, same class as `test/02_integration/app/mcp_stdio_integration_spec.spl`
(which requires `SIMPLE_MCP_TEST_BINARY` pointing at a native exe).

## Suggested remediation (pick one)

1. Make the fallback explicit: when the default self-hosted binary is
   missing AND the host triple is not `x86_64-unknown-linux-gnu`, emit
   `ERROR — nothing was checked (host-gated: no self-hosted <triple> binary;
   run after bootstrap)` instead of silently falling back to the seed and
   failing selftest with an engine-demotion message. A SKIP-class verdict
   (exit 2, distinct from FAIL) would let Windows pre-bootstrap CI aggregate
   honestly.
2. Or: teach the guards to accept `SIMPLE_BIN=<windows self-hosted path>`
   once stage 3 lands and document that in the guard headers.

## Related

- `doc/08_tracking/bug/smux_capture_pane_merged_history_2026_11_12.md`
  (same class: check requires runtime capabilities the current host lacks)
- Bootstrap lane producing the Windows self-hosted binary:
  `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap`
