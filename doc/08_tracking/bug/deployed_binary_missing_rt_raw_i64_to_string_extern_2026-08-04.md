# Deployed macOS binaries reject `rt_raw_i64_to_string` — entire host-compositor spec chain unrunnable

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Date:** 2026-08-04
- **Area:** tooling/deploy (extern registry of BOTH `bin/release/aarch64-apple-darwin-macho/simple` and its `simple_seed` sibling)
- **Symptom:** `semantic: unknown extern function: rt_raw_i64_to_string` fails whole-module load.

## Repro (isolated, one import, no compositor code)

```spl
use std.spec
use common.ui.native_scalar_text.{ui_native_i64_text}

describe "native scalar text extern probe":
    it "converts":
        expect(ui_native_i64_text(7)).to_equal("7")
```

`bin/simple test <probe>` -> `FAIL ... Error: semantic: unknown extern function: rt_raw_i64_to_string`.
`bin/release/aarch64-apple-darwin-macho/simple_seed run <spec>` fails identically.

The extern IS registered in the Rust runtime sources
(`src/compiler_rust/common/src/runtime_symbols.rs`,
`runtime/src/value/sffi/io_print.rs`), so both deployed binaries predate that
registration (stale extern registry — same failure class as the 07-16
"stale seed = old extern registry" note).

## Impact

`src/lib/common/ui/native_scalar_text.spl` is imported by
`os.compositor.host_compositor_core` (pre-existing `ui_native_i64_text` use),
so every spec that touches the hosted compositor chain fails at load, e.g.
`test/01_unit/os/compositor/host_gui_event_router_spec.spl` (all 5 examples,
including the 2 that predate 2026-08-04) and
`test/01_unit/os/compositor/compositor_content_registry_spec.spl`.

## Ask

Redeploy `bin/release/aarch64-apple-darwin-macho/{simple,simple_seed}` from a
build that includes the current runtime extern registry (stage4 deploy recipe:
driver + `-p simple-compiler-backfill` + no-LTO runtime last), or make the
interpreter treat an unknown extern DECLARATION as a load-time warning and only
fail on CALL (the whole-module-load failure on unknown extern decl is already
a known defect class, 07-18).
