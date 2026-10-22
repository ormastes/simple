# Result Optional value preservation

Requirement: REQ-ENUM-RESULT-OPTIONAL.
Source: `test/01_unit/compiler/mir/result_optional_unwrap_runtime_spec.spl`.
Four actual-value scenarios authored; all **UNRUN**. Manual authored without
docgen.

1. Call a real producer with Some(0), Some(3), and None. Require the receiver
   count to increase once per call, keep both integers present, and preserve
   absence.
2. Unwrap Optional false, 2.5, and Text payloads from Result, then unwrap the
   Optional. Require the original values without decoding the outer handle
   as its inner type.
3. Return `Result<ResultOptionalRecord?, text>`, unwrap it into an `if val`
   binding, and read both record fields. This exercises the same declared
   shape as the driver's final repository lookup without mocking that driver.
4. Unwrap Err(Some(3)) and Err(None) via `unwrap_err`. Require independent
   error selection and Optional presence.

The existing native test workflow also has two expected-failure entrypoints:

| Fixture | Required diagnostic |
|---|---|
| `test/fixtures/result_optional_unwrap_mismatch/main.spl` | ``called `.unwrap()` on an Err Result`` |
| `test/fixtures/result_optional_unwrap_err_mismatch/main.spl` | ``called `.unwrap_err()` on an Ok Result`` |

Both must fail before their `UNEXPECTED` marker and exit 91. Neither has been
run. Use a qualified changed pure-Simple producer and record its source/runtime
identity; a pre-change interpreter pass alone would not qualify native MIR
lowering. No seed fallback, new runner, or compiler build was launched.
