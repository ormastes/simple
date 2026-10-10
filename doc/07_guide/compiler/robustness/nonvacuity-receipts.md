# Non-vacuity receipts (compile lanes)

Robustness item 15a. A compile lane can return Success having lowered, emitted
or linked nothing (or fewer units than it accounted for), so whatever was built
on it passes over an empty artifact. The lane receipt makes that a failure.

Spec-level vacuity (a spec that evaluated zero expectations) is a separate
mechanism: `SPEC FILE VACUITY` in the test runner.

## Lane receipt

`src/compiler/80.driver/driver_pass_receipt.spl` — the same module and the same
sink as the pass receipts. One line per lane, appended to the file named by
`SIMPLE_PASS_RECEIPT` and written to the debug log:

```
lane_receipt name=native-build verdict=ok modules_seen=1163 modules_lowered=1163 modules_objectless=41 functions_emitted=58210 statics_emitted=912 objects_written=1122 link_inputs=1122 reason=-
```

(numbers illustrative). `verdict` is `ok`, `vacuous` or `mismatch`; `reason` is
the last field and runs to end of line.

| finding | condition | default |
|---|---|---|
| `vacuous` | `modules_lowered == 0`; executable lane with `functions_emitted + statics_emitted == 0`; `objects_written == 0`; `link_inputs == 0` | **fails the lane**: `E-LANE-VACUOUS: <lane> lane <reason> ...` |
| `mismatch` | `modules_lowered > modules_seen`; `objects_written + modules_objectless < modules_lowered`; `link_inputs < objects_written`; object/archive lane with zero functions and statics | warning (`non-vacuity: lane_receipt ...`) |

The check is a comparison of counts the lane already holds at its link
boundary. It adds no pass and reads no file.

### Switch

`SIMPLE_LANE_RECEIPT`:

| value | effect |
|---|---|
| unset / `error` | vacuity fails the lane; mismatch warns |
| `strict` | mismatch fails too (`E-LANE-COUNT`) |
| `warning` | receipt written, nothing fails |
| `off` | no counting at the call site, no receipt, no check |

### Where it is wired

`compile_to_native` in `driver_aot_native_output.spl`, after the per-module
outcome verdict and the existing zero-object guard, before emit-object /
archive / shared / link. `requires_code` is false for the three emit modes
(a declaration-only object is legal).

### Adding a lane

Build a `LaneReceipt` from counters the lane already has and return its
failure:

```simple
val lane_failure = record_lane_receipt(LaneReceipt(
    lane: "my-lane", requires_code: true,
    modules_seen: offered, modules_lowered: taken, modules_objectless: facades,
    functions_emitted: fns, statics_emitted: statics,
    objects_written: ok_units, link_inputs: objects.len()))
if lane_failure != "":
    return CompileResult.CodegenError(lane_failure)
```

Guard any counting loop with `lane_receipt_enabled()` so `off` skips the work.
The pure decision is `lane_receipt_check(receipt, level)`; test against that.

## Known limits

- The receipt is wired into `compile_to_native` only. The single-object
  bootstrap lane (`bootstrap_compile_context_to_native_local`), the grouped
  child mode (`native_group`, which returns per-member results before the link
  boundary) and the SMF / C / wasm / GPU backends do not emit one.
- Count mismatches warn by default; `strict` has not been run over a full
  self-hosted build.
- The seed's own Rust `native-build` is a separate implementation and emits no
  lane receipt.
