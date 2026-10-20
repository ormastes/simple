# native-build of an entry whose directory path contains a dot links without `__simple_main`

- Status: OPEN (workaround in scripts/check/check-stage-binaries-runnable.shs)
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2

## Observation

Pure-Simple bootstrap CLI (diagnostic Stage 2 relink `s2diag17`, sha256
61f1f47a37bc..., `--version` = `simple-bootstrap 1.0.0-rc.1`), run from a
repo root, on the three-line hello world used by the stage-binary runnable
gate (`fn main() -> i64: print "hi"; 0`):

| source path | native-build rc |
|---|---|
| `<tmp>/nodot1/hello.spl` | 0 (binary prints `hi`) |
| `<tmp>/a-b/hello.spl` | 0 |
| `<tmp>/dot.1/hello.spl` | 1 |
| `<tmp>/g.1/sub/hello.spl` | 1 (dot in a grandparent) |

The failing runs end with

```
error: in-process native-build: LLVM native linking failed: Linking failed:
cc linking failed: ld.lld: error: undefined symbol: __simple_main
>>> referenced by simple_entry.c
```

So the entry module's `main` is not emitted as `__simple_main` when any
directory component of the source path contains a `.`. The likely cause is a
module name derived from the path and split on `.`, but this has not been
traced in the source.

## Impact

`check-stage-binaries-runnable.shs` probed from `$TMPROOT/probe.N` under a
`mktemp` directory named `<name>.XXXXXX`, so every pure-Simple bootstrap
binary FAILed its `native-build` probe even when it works.

## Workaround

The gate's probe and temp directories now use `_` instead of `.`
(`# @workaround bug=native_build_entry_main_undefined_when_source_path_has_dot_2026_10_20`).
A `TMPDIR` that itself contains a dot still reproduces it.
