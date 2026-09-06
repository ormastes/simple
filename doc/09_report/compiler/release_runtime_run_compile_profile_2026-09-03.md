# Release runtime run/compile diagnosis and profile

## Subject

`/Users/ormastes/simple/bin/release/macos-arm64/simple`, reporting
`Simple v1.0.0-rc.1`, on macOS arm64.

## Source execution

A one-line valid fixture (`print "hello"`) exits 1 and emits only
`[STDERR] Error running ...`. The traced route is:

```text
CLI run -> _cli_driver_binary -> repository bin/simple launcher
        -> old simple-bootstrap 1.0.0-beta -> unsupported run command
        -> generic outer CompileResult fallback
```

The source fix replaces this with an in-process interpreter route and preserves typed
external-process failures where the compatibility facade is still used.

## Minimal native compilation

Command shape:

```text
simple native-build /tmp/tiny.spl -o /tmp/tiny
```

Observed once:

| Measure | Result |
|---|---:|
| Wall time | 1.32 s |
| Reported compile | 0.0 s |
| Reported link | 1.3 s |
| User CPU | 0.20 s |
| System CPU | 0.54 s |
| Maximum RSS | 32,440,320 bytes |
| Input units | 1 |
| Fabricated unresolved stubs | 652 |
| Produced size | 85,296 bytes |
| Produced program exit | 3 |

This is **not a valid successful compilation**. The deployed executable predates the
current fail-closed stub policy: even with `SIMPLE_NO_STUB_FALLBACK=1`, it fabricates
652 symbols, exits zero, and emits a program that exits 3.

## Hot-path assessment

For the minimal invalid build, linking consumes approximately 98% of reported wall
time. Frontend/codegen time rounds to zero, so optimizing parser or MIR work cannot
materially improve this specific path. The immediate priorities are:

1. rebuild from current source so unresolved internal symbols fail before linking;
2. supply/admit the correct runtime archive instead of compiling a 652-stub object;
3. avoid subprocess interpreter startup by using the in-process run API;
4. only then profile valid cold/warm compile and incremental-cache paths.

The broad command with `--source src/compiler --source src/app --source src/lib`
also scanned/compiled unrelated modules and eventually aborted in native codegen. That
command is not representative for a tiny program; `--entry-closure` or the minimal
single-source form is required for a fair compile-speed measurement.

The repository optimizer command exited 133 under this deployed runtime, so no
optimizer success is claimed.

