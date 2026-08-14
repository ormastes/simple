# Simple web example qualified-import HIR `ANY` failure

Status: fixed in source; fresh admitted compiler execution pending

Owner: standalone Simple web example source-root boundary

## Reproducer

Cross-building `examples/06_io/simple_web_server/main.spl` with
`examples/06_io/simple_web_server` as an explicit source root reported that
`examples.simple_web_server.config` and `.routes` could not be resolved. HIR
then erased `ServerConfig` to `ANY` and stopped on field `static_root`.

The example directory is the declared resolver root, so sibling modules are
`config`, `routes`, `static_files`, `error_pages`, and `middleware`. They are
not members of a synthetic `examples.simple_web_server` package.

## Fix and regression

`main.spl` and `routes.spl` now use source-root-relative sibling imports.
`test/01_unit/examples/simple_web_server/source_root_import_contract_spec.spl`
fences both the exact main failure and the adjacent route dependency graph.
A bounded diagnostic cross-build passed HIR and object generation after this
change; it then stopped at the separate target-runtime link boundary.

## Remaining target prerequisite and exact resume

Do not use the connected board's Debian root filesystem as SimpleOS evidence.
Resume only when an admitted current pure-Simple CLI and a canonical QRB2210
SimpleOS boot/download owner exist. Build the recoverable AArch64 artifact on
the host with:

```sh
SIMPLE_RUNTIME_PATH=none <admitted-simple> native-build --target aarch64-unknown-linux-gnu --backend llvm --runtime-bundle core-c-bootstrap --source examples/06_io/simple_web_server --source src/lib --entry-closure --mode dynload --entry examples/06_io/simple_web_server/main.spl --output build/unoq/simpleos-rootfs/usr/bin/simpleos-web-server
```

Then boot that source-matched rootfs through the future canonical QRB2210
SimpleOS boot/download owner and run its live server receipt collector. No such
boot/download owner or server collector exists at this revision, so there is no
honest physical execution command to substitute. The existing graphics-only
probe remains:

```sh
flock /tmp/unoq-server-matrix.lock env SIMPLE_BIN=<admitted-simple> sh scripts/check/run-unoq-qrb2210-native-2d-live.shs --device 3655308719
```

It must stay blocked until `/usr/bin/simpleos-unoq-2d-evidence` is supplied by
the SimpleOS image; a Debian-side file never satisfies that prerequisite.
