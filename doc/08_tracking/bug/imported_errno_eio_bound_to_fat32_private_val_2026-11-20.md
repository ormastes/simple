# Imported `EIO` resolves to the Fat32 module's private `-5` in a spec

- Date: 2026-11-20
- Found by: DHR P6 kernel replay work (PR #10516), `bin/simple.exe test` on Windows
- Status: open, not minimized

## Observed

`test/03_system/tools/replay_kernel_fail_closed_spec.spl` imported
`use os.kernel.errno.{EIO}` (`src/os/kernel/errno.spl`: `val EIO: i32 = 5`).
Both of these evaluated to `5`, not `-5`:

```simple
expect(r).to_equal(-(EIO as i64))
expect(r).to_equal(0 - (EIO as i64))
```

So the spec's `EIO` was `-5`. That is the value of the PRIVATE
`val EIO: i32 = -5` in
`src/os/kernel/fs/_Fat32Filesystem/types_and_names.spl`, which is
co-compiled into the same test. An explicitly imported name was bound to
another module's private constant with the same name.

In the same run, `src/os/kernel/replay/hooks.spl` (which imports the same
`EIO` the same way) got `5`. Its `-(EIO as i64)` produced `-5`, which is correct.

## Workaround in use

The spec checks the literal `-5`, commented as `-EIO`.

## Next step

Minimize: two modules that each define a private `val EIO` with different
values, plus a third module that imports one of them explicitly. Then check
which value the import binds to, under both the test runner and `run`.
