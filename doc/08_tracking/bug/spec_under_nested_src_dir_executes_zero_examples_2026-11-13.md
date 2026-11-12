# Specs below a test directory that contains `src` execute 0 examples (2026-11-13)

Status: FIXED in the seed module resolver (same change). A second, separate
cause of "0 examples" is described at the end and is NOT fixed here.

## Symptom

```
$ simple test test/01_unit/lib/nogc_async_mut/container/windows_docker_engine_codec_v3_spec.spl
error: SIMPLE_JIT_STRICT: HIR lowering error: cannot resolve import
  `test.fixtures.orchestration.simple_container_windows_adapter_fixture_v2`:
  ... module path segment `test` not found ...
  help: check that the module exists at "test/01_unit/lib/nogc_async_mut/container/test"
error: test-runner: no examples executed
SPEC FILE VERDICT: ... outcome=ERROR declared>=18 executed=0 passed=0 failed=0
```

The verdict is `ERROR` and the exit code is 1 -- a 0-example run is never
counted as a pass -- but no example runs, so the file's real results are hidden.

## Cause (two steps)

1. `203f43bc0c6` ("stop leaking mode env pins into spec-example children")
   made the runner set the scrub marker in its own environment and then spawn
   the spec child through `_process_run_bounded_raw`, which scrubs when that
   marker is active. So the SPEC CHILD itself lost `SIMPLE_EXECUTION_MODE` /
   `SIMPLE_RUNTIME_MODE` (and the marker) and now runs on the default JIT-first
   lane instead of the pinned one. Proven: reverting that commit in the
   working tree restores `executed=18` for the spec above.
2. On the JIT lane the seed's module resolver takes the nearest ancestor that
   contains a `src` directory as the project root. The test tree mirrors
   `src/lib/<x>/src` as `test/01_unit/lib/<x>/src` (four such directories), so
   for a spec below `test/01_unit/lib/nogc_async_mut/` the "project root" is
   that test directory, `<root>/test` does not exist, and `use test.fixtures.*`
   is unresolvable. An unresolvable import is a hard error there (by design:
   `1478ca64460`), so nothing falls back to the interpreter.

## Scope

256 specs import `test.fixtures.*`. 27 of them live below one of the four
nested-`src` trees (`nogc_async_mut` 21, `nogc_sync_mut` 6). On origin all 27
executed 0 examples.

## Fix

`ModuleResolver::resolve` (`src/compiler_rust/compiler/src/module_resolver/resolution.rs`):
when a top-level namespace is not found under the detected project root, try
the enclosing ancestors that also contain `src`. Last resort only, so no import
that resolves today changes. Test:
`test_resolve_project_namespace_through_an_enclosing_root` (red before with the
exact production message).

After the fix, on the 27 specs: 22 `outcome=OK`, 1 runs all 18 examples with
one genuine failure (the spec above), 4 still execute 0 for the reason below.
No spec got worse.

## Not changed: the runner still strips the pins from the spec child

Restoring the pins (spawning the spec child through an unscrubbed helper) was
tried and NOT landed: it puts spec children back on the interpreter lane,
whose module loader makes an import of a PRIVATE function fatal, and specs that
pass today then execute 0 examples (`macro_array_insert_native_spec`,
`database_optional_receiver_prefix_spec`, `global_write_visible_to_callee_spec`
in a 30-spec sample). That is the pre-`203f43bc0c6` behaviour, but it is a
worse result than origin's. Which lane a spec child should run on is an owner
decision.

## Second cause of "0 examples", still open

A spec whose JIT compile falls back to the interpreter for an ordinary reason
then hits the interpreter's fatal private-import check, e.g.
`host_runtime_exec_begin_v3_spec.spl`:

```
error: semantic: private fn `distributed_grant_signature_message_v2` of module
  `std.nogc_sync_mut.daemon_sdk.distributed_grant_verification_v2` ... is not visible
error: test-runner: no examples executed
```
