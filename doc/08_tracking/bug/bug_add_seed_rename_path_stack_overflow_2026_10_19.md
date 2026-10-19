# bug-add on the Rust seed overflows the stack in rename_path

- Status: OPEN
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Blocks: recording bugs with `bug-add` while no self-hosted full CLI exists
  (the bootstrap lane had to add its bug_db.sdn rows by hand and reseal).

## Observation

With the Rust seed built from `release_phase3` @ `84e13d92794` + this lane:

```sh
SIMPLE_RUST_SEED_WARNING=0 <seed> run src/app/bug_add/main.spl \
  --id=<id> --severity=p1 --title=<t> --file=<path> --line=1 --repro=<md> --date=2026-10-19
```

prints `error: stack overflow: recursion depth 1000 exceeded limit 1000 in
function 'rename_path'` and leaves `doc/08_tracking/bug/bug_db.sdn`
unchanged. The save path reaches `rename_path`
(`src/lib/nogc_sync_mut/io_runtime.spl:493`), whose only body is
`rt_file_rename(old_path, new_path)`; on the seed interpreter that extern
call resolves back into a Simple `rename_path`/`file_rename` wrapper instead
of the runtime, so it recurses until the depth limit.

The same command on the older seed (base `630f773bdc7`) could not run at all:
it failed to parse `src/lib/common/encoding/external_text.spl` (the
`unit = ...` seed parser issue, fixed upstream by #3804).

## Not yet established

Which wrapper the seed's extern dispatch picks for `rt_file_rename`.
