# `test/01_unit` "Process exited with code 1" cluster (2026-08-26)

**Status:** runner-side opacity FIXED (this commit); the 102 underlying spec
failures remain OPEN as genuine behavioural REDs (see buckets below).

## Symptom

A full `test/01_unit` sweep (`scratchpad/full01.out`, seed binary
`bin/release/x86_64-unknown-linux-gnu/simple`, 60744944 bytes, mtime
2026-08-26 01:16) reported **102** specs as

```
  FAIL  <spec> (...)
  Error: Process exited with code 1
```

with no further text. All 102 are exit code 1 (no other code appears).
Directory histogram: `lib/common` 42, `lib/hardware` 7, `lib/crypto` 7,
`lib/std` 6, `lib/nogc_sync_mut` 3, `std/feature_validation` 2,
`lib/structural` 2, `lib/js` 2, `lib/gc_sync_immut` 2, `lib/editor` 2,
`browser_engine/net` 2, 25 singletons. Twin state: 40 byte-identical
`test/unit` twins, 23 diverged, 39 no twin.

## Root cause (mechanical, one defect for all 102)

`extract_error_message` in
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` only recognised
compiler/runtime shapes (`semantic:`, `parse error:`, `compile failed:`,
`ERROR:`, `Error:`, `error:`, `unsupported path call:`, `not found`). A child
that ran to completion and failed a plain `expect(...)` prints

```
  ✗ <example name>
    expected <got> to <matcher> <want>
```

which matched nothing, so `make_result_from_output` fell back to
`"Process exited with code {exit_code}"`. Every one of the 8 sampled specs
(8 different directories) reproduced this: `bin/simple run <spec>` shows real
`✗` lines, `bin/simple test <spec>` in the parallel/directory path shows only
the exit code.

**Fix:** a fallback pass in `extract_error_message` that, when the primary
pass found nothing, returns the first `✗ ...` line joined with the
`expected ...` line directly below it (ANSI stripped). Primary error lines
still win. Specs (both pass; the first fails 3/4 pre-fix):

- `test/01_unit/lib/test_runner/assertion_failure_surfaced_not_exit_code_spec.spl` (reproduce)
- `test/01_unit/lib/test_runner/error_line_precedence_neighbors_spec.spl` (neighbours)

Existing `terminated_vs_crashed_spec` and `truncated_capture_fail_closed_spec`
still pass (5/5, 7/7). Stdlib is read as source, so no rebuild is needed.

## Real-error histogram of the 8-spec sample

Every sample is a **behavioural assertion failure** -- none is a wrong import,
missing export, bad annotation, stale fixture id, or missing `use`. There is
therefore no mechanical spec-side sub-cluster to fix; per
`.claude/rules/testing.md` these specs stay RED.

| bucket | n | representative spec | exact error |
|---|---|---|---|
| value mismatch in product logic | 4 | `test/01_unit/lib/common/bytes/bytes_foundation_spec.spl` | `✗ U32be + U32le serialized into a buffer CRC matches a recomputed CRC -- expected 0 to equal 154` |
| | | `test/01_unit/lib/nogc_sync_mut/game2d/ports/doomgeneric_spec.spl` | `expected 180 to equal 12` |
| | | `test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl` | `✗ should pull dirty producers into the incremental island selection -- expected [4] to equal [1, 4]` |
| | | `test/01_unit/browser_engine/net/cors_spec.spl` | `✗ AC-5: aggregate safelisted values cross at 1025 bytes -- expected accept to equal accept, content-language` (+2 more AC-5) |
| crypto known-answer mismatch | 1 | `test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl` | `✗ TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...` (all 3 KATs; X448 output bytes differ) |
| generated-text mismatch | 1 | `test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl` | `✗ AC-2: generated SV declares AXI AWADDR port` (+WDATA, ARADDR; header comment emitted, port lines absent) |
| callback never fired | 1 | `test/01_unit/lib/std/concurrency/promise_spec.spl` | `✗ executor receives both callbacks -- expected subject to be truthy, got false` |
| engine-routing probe | 1 | `test/01_unit/std/feature_validation/codegen_spec.spl` | `✗ proves each arm reached the engine it names -- expected codegen feature-validation probe (#100 / #95 / #96) ...` |

`doomgeneric_spec` additionally logs
`[WARN] Failed to load imported types from ["std","spec"]: ... resolves from the project stdlib roots only`
before the assertion, but the failing oracle is the value mismatch.

## Next

Re-run the sweep on a tree carrying this fix; every one of the 102 lines will
now name its failing example, so the remaining 94 can be bucketed by owner
without per-spec reruns. Each bucket above needs its own bug record with the
implementation file:line once triaged.

## Unrelated, observed while verifying

Directory-mode `bin/simple test <dir>` on a pristine `origin/main` checkout
(`0861983da93`) aborts with
`error: semantic: variable \`mcdc_dynamic_probe_controller_load_builtin_current_owner\` not found`
(introduced by `98215e0f708`, `src/lib/nogc_sync_mut/mcdc/dynamic_probe.spl`)
on the 2026-08-26 seed. The shared worktree that ran the sweep carries an
uncommitted local edit removing that MCDC block, which is why the sweep ran.
Not addressed here.
