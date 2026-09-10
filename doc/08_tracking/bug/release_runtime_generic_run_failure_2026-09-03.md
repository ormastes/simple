# Release runtime hides source execution failure

## Status

Source fixed; deployed `v1.0.0-rc.1` requires rebuilding before the corrected path is active.

## Reproduction

```text
$ printf 'print "hello"\n' >/tmp/tiny.spl
$ bin/release/macos-arm64/simple run /tmp/tiny.spl
[STDERR] Error running /tmp/tiny.spl
$ echo $?
1
```

The deployed release executable selected the repository `bin/simple` launcher as an
external driver. That launcher executes the older
`bin/release/aarch64-apple-darwin-macho/simple` (`simple-bootstrap 1.0.0-beta`),
which does not support the `run` command. The outer CLI discarded that concrete
failure behind the wildcard `CompileResult` message.

## Root cause

Three independent defects combined:

1. A deployed release executable could select the repository launcher as a driver.
2. The source run command imported the lightweight subprocess interpretation facade
   rather than the existing in-process interpreter API.
3. The facade converted some nonzero child exits into `CompileResult.Success`.

## Resolution

- Release executables reject the mutable repository launcher as a driver candidate.
- `cli_run_file` uses `compiler.driver.driver_api_interpret.interpret_file` directly.
- The lightweight facade preserves every nonzero child exit as `RuntimeError`, including
  executable name, exit status, and captured detail.
- The impossible wildcard result now reports executable/source ABI skew explicitly.

The existing executable cannot acquire source changes without a rebuild. Until then,
its `run` result remains unqualified and must not be treated as a source-program error.

