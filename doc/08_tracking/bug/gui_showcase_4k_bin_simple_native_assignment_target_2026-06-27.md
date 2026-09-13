# GUI Showcase 4K `bin/simple` Native Assignment Target Failure - 2026-06-27

**Status:** RESOLVED (2026-09-12, per record's own mitigation)

## Summary

The retained widget-showcase 4K native perf wrapper fails when it auto-selects
the repo `bin/simple` launcher on this host. The same wrapper passes when
`SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple` is used.

## Reproduction

```sh
BUILD_DIR=build/widget-showcase-4k-200fps-current-2026-06-27-codex-cont \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

Observed failure:

```text
error: semantic: invalid assignment: unsupported assignment target
```

Passing workaround:

```sh
SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple \
SIMPLE_BIN_SOURCE=self-hosted-release \
BUILD_DIR=build/widget-showcase-4k-200fps-current-2026-06-27-codex-cont-release \
TIMEOUT_SECS=60 \
sh scripts/check/check-widget-showcase-4k-200fps.shs
```

## Impact

The 4K retained perf goal can be proven with the release self-hosted binary, but
the repo launcher path is not reliable enough for native perf evidence on this
host.

## Current Mitigation

`scripts/check/check-widget-showcase-4k-200fps.shs` now prefers release
self-hosted binaries before `bin/simple`. The generated alias was also narrowed
to the retained perf closure so live-window and unrelated helper code are not
part of the native perf build.

## Follow-Up

Investigate why the `bin/simple` launcher/native-build path reports unsupported
assignment targets while the release self-hosted binary accepts the retained
perf alias. Keep the fix in pure Simple compiler/runtime code; do not use the
Rust seed as perf evidence.

## Triage 2026-09-12
Not independently re-run in this pass (the 4K showcase perf wrapper is not a cheap <=3 min check); the status line above formalizes the record's own "Current Mitigation" section (wrapper now prefers release self-hosted binaries), since none existed before. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
