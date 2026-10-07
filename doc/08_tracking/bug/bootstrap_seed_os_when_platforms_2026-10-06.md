# Seed rejects Linux OS branches during Phase 2 discovery

The ad hoc Linux restart from fa5d0bd171bc94ffec99d6c974d27e6c346e39ef completed four Rust builds and all five preflight checks, then failed Phase 2 before native compilation. Discovery of `src/lib/nogc_sync_mut/io/path_identity_abi.spl` rejected `@when(os="linux")` at line 20. The terminal build receipt records exit 1, quiescent children, and peak RSS 3552388 KiB; this is a preprocessing failure rather than an RSS failure.

`pipeline/cfg_strip.rs::strip_os_when_blocks` recognized only the Windows branch. Add Linux, FreeBSD and macOS matching while retaining fail-closed rejection of unsupported directives. A focused regression preprocesses the actual ABI file for all four hosted targets, verifies exactly one errno owner, preserves line count, and parses the filtered source. Existing malformed-block tests remain required.

Evidence: `/tmp/simple-adhoc-restart-20261006/build.log`, `build.rss.env`, and `stage3/x86_64-unknown-linux-gnu/stage2-command.transcript`. Repair verification: `/tmp/simple-os-when-repair/tests.log` and `tests.rss.env`; four focused tests passed, tool exit 0. Phase 2 remains unadmitted until the repaired generation succeeds through its native verification matrix. No Phase 3/4 or release claim follows from the focused test.
