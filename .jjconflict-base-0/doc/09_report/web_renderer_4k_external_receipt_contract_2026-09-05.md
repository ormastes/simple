# External 4K showcase receipt contract

Run `sh scripts/check/check-web-showcase-4k-receipt.shs` on an admitted host.
The optional `--binary` argument accepts only a resolved deployed
`bin/release/<triple>/simple` path. Rust seeds and `bin/local` are rejected.
The default macOS ARM64 target is the deployed `aarch64-apple-darwin-macho`
binary. No build is performed.

Each invocation creates a fresh retained directory under
`build/web_renderer_vulkan_4k_showcase_hardening/simple/receipt.*` with
`receipt.env`, bounded CLI logs, and the tracked source diff. The receipt binds
the exact executable, input HTML, runner source, SHA-256 digests, source revision,
4K viewport, requested Vulkan backend, and measurement boundaries. The tracked
diff does not identify untracked source or the full imported closure; the full
closure and composed fixture digests therefore remain explicitly unavailable.

Version/help probes are limited to three seconds each. A bootstrap identity,
missing `run` command, missing executable or missing timer yields `BLOCKED`
(exit 2), with no renderer execution. An executable renderer run is headless,
limited to 20 seconds plus a one-second kill grace, and records external
process wall seconds and maximum RSS in bytes. This interval includes source
execution and ends at process exit; it is not production cached-artifact startup,
first presentation, or scanout latency. macOS RSS is already bytes; Linux GNU
time reports KiB and is converted explicitly.

The stdout checker requires one terminal 3840×2160, 8,294,400-pixel Vulkan
device-readback record, nonzero checksum/variation and positive device/handle
identities. Nonzero process exit, timeout, changed inputs, missing metrics,
fallback or malformed readback yields `FAIL` (exit 1). Valid readback produces
`MEASURED` evidence but still exits 2 because physical-device admission,
presentation completion, warm samples and all-tab Chrome parity are missing.
No execution path emits a full performance PASS or `comparison_admitted=true`.

Recheck retained metadata using
`sh scripts/check/check-web-showcase-4k-receipt.shs --check <receipt.env>`.
This detects missing/duplicate required keys and stale executable/fixture/runner
digests for measured rows; it is not an authenticated hardware receipt validator.
The wrapper was syntax-checked only during this change. No renderer measurement
or additional compiler probe was run.
