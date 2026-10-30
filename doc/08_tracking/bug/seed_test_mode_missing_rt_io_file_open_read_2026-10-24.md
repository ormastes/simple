# Seed `test` mode lacks extern `rt_io_file_open_read`

Status: open. Found 2026-10-24 while adding SourceReader specs (PR #4360).

## Symptom
Under the Rust seed's `test` command, any spec that reaches
`std.io_runtime.file_read` fails with
`semantic: unknown extern function: rt_io_file_open_read`. The same library
call works under the seed's `run` command (`simple.exe run src/app/cli/tldr_entry.spl ...`
read and wrote files successfully in the same session).

## Repro
Seed: `C:/dev/wt-rel3-new/build/c/db0e8ac7fe87/x86_64-pc-windows-gnullvm/bootstrap/simple.exe`
(Windows, gnullvm), at release/1.0.0 `a5bb914ffcd`.

```
simple.exe test test/01_unit/compiler/driver/source_reader_v1_spec.spl
#   2 of 3 examples fail: unknown extern function: rt_io_file_open_read
simple.exe test test/01_unit/app/cli/focused_native_build_env_owner_contract_spec.spl
#   same error (pre-existing spec, unrelated to #4360)
```

## Impact
Specs exercising real file I/O through `std.io_runtime` cannot be validated
on the seed's test lane; workaround in specs is a direct
`extern fn rt_file_read_text`. Not a defect in the code under test.

## Fix direction
Register `rt_io_file_open_read` (and siblings used by `file_read_result`) in
the seed interpreter's extern table for the test lane, matching the `run`
lane.
