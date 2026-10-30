# DevHub CLI process acceptance

The executable specification is
`test/03_system/app/devhub/feature/devhub_cli_process_spec.spl`.
It uses current SSpec `step` scenarios and built-in matchers. Each scenario
starts the production executable through `std.process.run` and checks its
exit code and output. No backend credentials or network access are needed.

Set `DEVHUB_SYSTEM_BIN` to the absolute path of the source-matched compiled
`src/app/devhub/main.spl` executable. An empty setting fails; it never skips.

| Requirement | Actual process behavior |
|---|---|
| REQ-CLI-001 | Help, empty arguments, and JSON version complete successfully |
| REQ-CLI-002 | Unknown command exits 1; invalid log mode and surface fail before dispatch |
| REQ-CLI-003 | Both OAuth clients encode UTF-8 octets and escape form separators |
| REQ-CLI-004 | Native millisecond and timestamp aliases use Unix wall-clock units |
| REQ-CLI-005 | Result tuple slots preserve native integer widths and signedness |
| REQ-CLI-006 | The Windows owner retains child failure and proves tree cleanup |
| REQ-CLI-007 | DEFLATE stored-block parsing rejects invalid offsets, truncation, and NLEN |

REQ-CLI-003 has focused production-helper regressions in
`test/01_unit/app/devhub/oauth_form_encoding_spec.spl` for Unicode, separators,
empty values, and unreserved ASCII. These are unit checks, separate from the
actual CLI process acceptance above.

REQ-CLI-004 is covered by `test/01_unit/lib/io/wall_clock_alias_spec.spl`
and its native build/run companion under
`test/fixtures/devhub/native_wall_clock_alias/`. The companion validates linking
and the real provider; it does not replace compiled SSpec execution.

REQ-CLI-005 has focused MIR classifier scenarios in
`test/01_unit/compiler/mir/result_native_integer_slot_spec.spl` and an actual
build/run fixture in `test/fixtures/devhub/native_result_unsigned_tuple/`.
The existing stage-3 compiler fails that fixture on the u64 slot; the repaired
compiler must build it and execute its high-bit and error-propagation checks.

REQ-CLI-006 is an actual child-process scenario in
`devhub_owned_process_spec.spl`, backed by the production-owner companion in
`test/fixtures/devhub/windows_owned_child/`. Set
`DEVHUB_OWNED_PROCESS_PROBE_BIN` to that source-matched compiled companion and
`DEVHUB_PROCESS_PROBE_DIR` to a fresh private directory for its captures.
Set `DEVHUB_PROCESS_PROBE_CHILD_BIN` to the compiled native `child.spl` fixture.
The companion starts a real child, polls its JobObject, and verifies collection;
missing artifacts or inputs fail rather than skip.

REQ-CLI-007 replaces a stale source-string guard with production parser calls in
`test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_negative_offset_guard_spec.spl`.
Its native companion under `test/fixtures/devhub/native_deflate_block/` checks
the compiler dependency's guard paths without replacing SSpec acceptance.

Run with the existing standalone Simple test runner using
`--native-backend=llvm --assert-ran --no-cache --no-db --no-session-daemon --sequential --keep-artifacts --verbose`.
Pin `SIMPLE_BINARY` to the admitted compiler and retain build/run output.
Generate the manual with `simple spipe-docgen <spec> --output doc/06_spec --no-index`;
require zero stubs. Test discovery or source inspection alone is not acceptance.

Current status: authored, execution and generated manual pending. The locally
available stage-3 bootstrap compiler supports native-build but has no test
or spipe-docgen command. Its production DevHub build is being attempted first.
