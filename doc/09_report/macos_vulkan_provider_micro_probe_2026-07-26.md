# macOS Vulkan Provider Micro-Probe

## Status

- status: fail
- reason: self-hosted-native-build-illegal-instruction
- scope: direct provider diagnostic only; no renderer or window launch
- host: Darwin 25.5.0 arm64
- base revision: `801c8caa6e1de793ab98a22616ff815f2db87f62`

## Inputs

- canonical self-hosted compiler:
  `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`
- compiler SHA-256:
  `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc`
- exact local provider dylib:
  `/Users/ormastes/simple/build/sffi/libsimple_runtime_wm.dylib`
- provider SHA-256:
  `a3e76424d824669afb1d5af17566225536153337070de10fd79a4b70ca337aec`

## Evidence

The focused source contract passed:

```text
PASS macos_vulkan_provider_micro_probe_contract_spec.spl (2 passed)
```

The native build failed before producing or launching the probe:

```text
Illegal instruction: 4
runtime error: field access on nil receiver
vulkan_provider_probe_wrapper_status=fail
vulkan_provider_probe_wrapper_reason=native-build-failed
```

Retained local artifacts:

- `build/macos_vulkan_provider_micro_probe/native-build.log` — 44 bytes,
  SHA-256 `dac6c14935953df43b1bf83a677ef069ee62367514d859ed719397b43a0938f0`;
  retained excerpt: `runtime error: field access on nil receiver`.
- `build/macos_vulkan_provider_micro_probe/evidence.env` — 244 bytes,
  SHA-256 `231b31004da0744ba6d409778dc772524c9f74b4346dd7bf05ad1b136c816f62`.

Future checker attempts retain no unbounded native-build transcript. Evidence
records an exactly shell-quoted `env` + compiler + argument command and hashes
a deterministic complete transcript through 8 KiB, then a 4 KiB head plus 4
KiB tail transcript (8,256-byte hard cap), adding an omission marker only when
compiler output exceeds that bound.

Not produced because the native probe never launched:

- `rt_vulkan_provider_is_available` result
- `rt_vulkan_provider_device_count` result
- dyld provider resolution
- loader error from probe execution
- provider error from `rt_vulkan_get_last_error` (the symbol is resolved, but
  its text ABI is intentionally blocked until DynLib gains a typed text call)

No full-live Vulkan command, window, framebuffer, or input evidence was
attempted. The three-cycle micro verification limit was reached, so this
report does not claim provider admission or device enumeration.

The subsequent manifest-admission repair was static only. The checker now
selects the manifest-recorded compiler/provider through the shared canonical
admission contract, requires current repository/source provenance and exact
hashes, and rejects seed/debug artifacts and caller path overrides. It did not
run a fourth native build or reopen the exhausted three-cycle limit.
