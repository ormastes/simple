# wine_hello_fixture_spec.spl: imports 4 symbols that no longer exist (orphaned from an old Wine-exe-probe API)

**Status:** Open
**Category:** GENUINE-BUG (API drift — not a simple rename; result shape changed)
**Discovered:** 2026-07-20 (whole-suite triage campaign, shard meas_01u_03)

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib_standalone/common/.spipe_matchers_wine_hello_fixture_spec.spl --no-session-daemon
```

```
Wine hello fixture
  ✗ builds the known executable milestone fixture
    semantic: function `wine_hello_exe_probe` not found

1 example, 1 failure
FAIL test/01_unit/lib_standalone/common/.spipe_matchers_wine_hello_fixture_spec.spl
```

## Full spec (unedited, 11 lines)

```
use common.wine_hello_exe.{wine_hello_exe_probe, wine_hello_exe_can_execute}
use common.wine_hello_fixture.{wine_known_hello_exe_fixture_bytes, wine_hello_fixture_verified_gates}

describe "Wine hello fixture":
    it "builds the known executable milestone fixture":
        val result = wine_hello_exe_probe(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates())
        expect result.status == "executed"
        expect result.stdout == "Hello from SimpleOS Wine\n"
        expect result.stdout_handle == -11
        expect result.bytes_written == 25
        expect result.exit_code == 0
        expect wine_hello_exe_can_execute(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates()) == true
```

## Root cause: 4 imported symbols do not exist in current source

`src/lib/common/wine_hello_exe.spl` (full file, 34 lines) exports only:
- `class WineExeProbeResult` with fields `status, error, stdout, exit_code`
  (**no** `stdout_handle` or `bytes_written` fields)
- `fn wine_hello_exe_probe_manifest_evidence_vm(exe_bytes, precondition_manifest,
  execution_evidence, space: WineVmProcessSpace, load_addr, stack_addr,
  heap_size, stack_size) -> WineExeProbeResult` (8-arg signature)

It does **not** export `wine_hello_exe_probe` (2-arg form the spec calls) or
`wine_hello_exe_can_execute` at all.

`src/lib/common/wine_hello_fixture.spl` exports only:
- `wine_known_hello_exe_fixture_bytes()`
- `wine_hello_fixture_precondition_manifest()`
- `wine_hello_fixture_execution_evidence_struct()`

It does **not** export `wine_hello_fixture_verified_gates` at all.

## Why this is NOT a simple rename fix

This isn't "old name -> new name with the same shape" (which would be a safe
STALE-TEST fix). The API materially changed:
- The probe function grew from 2 args (`exe_bytes, gates`) to 8 args
  (`exe_bytes, precondition_manifest, execution_evidence, space:
  WineVmProcessSpace, load_addr, stack_addr, heap_size, stack_size`), adding
  a `WineVmProcessSpace` dependency the spec has no way to construct without
  inventing test data not present anywhere in the spec today.
- The result struct dropped `stdout_handle` and `bytes_written` fields
  entirely — there is nothing to rename these assertions to; the current
  `WineExeProbeResult` simply doesn't carry that information.
- `wine_hello_exe_can_execute` and `wine_hello_fixture_verified_gates` have
  no successor of any name in their respective modules — they appear to have
  been removed outright, not renamed.

Per the campaign guide, weakening/dropping assertions to force green is
forbidden, and guessing new required args/removed-field replacements would
either fabricate test data or silently drop coverage — so this is filed as
GENUINE-BUG (orphaned spec / API drift) rather than "fixed."

## Suggested fix

Either:
1. Rewrite the spec against `wine_hello_exe_probe_manifest_evidence_vm`,
   constructing a `WineVmProcessSpace` (see `std.common.wine_vm_adapter`) with
   `ok: true, version: <nonzero>, pid: <nonzero>, capabilities: ["pid"]` per
   the guard checks in `wine_hello_exe_probe_manifest_evidence_vm` (lines
   29-32), and drop/rederive the `stdout_handle`/`bytes_written` assertions
   against whatever fields the current `WineExeProbeResult` actually has; or
2. If the 2-arg `wine_hello_exe_probe`/`wine_hello_exe_can_execute` surface
   was intentionally removed and this milestone fixture is obsolete, delete
   the spec (requires explicit user approval per project rules — not done
   here).

## Affected specs

- `test/01_unit/lib_standalone/common/.spipe_matchers_wine_hello_fixture_spec.spl` (sole affected spec in this shard)
