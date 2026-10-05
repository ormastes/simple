# Cranelift Win64 large frames skip the stack guard page

Status: provider fix validated in an isolated native harness; full provider
rebuild and original Simple scalar fixture verification remain pending.

## Observed failure and selected owner

The `scalar-probe-sdk2/cranelift/numeric_payload_boundary_trace` retained object
has `__simple_main` beginning with `sub rsp, 0xe4a0` (58,528 bytes), followed by
callee saves and local writes, before its first reporting call. No intervening
stack probe is present. The executable raises `0xc0000005` before its first
marker; the LLVM-produced fixture reaches the markers. This is evidence of a
prologue hazard, **not a captured exception PC for the original executable**.

The producer is `p2-next407be-sdk-relink1/compiler.exe`, SHA-256
`27ac2358f22f28c9a43ec3ab47ac3957d5e2b293fc8b44fc52e573512f0c4c69`.
Its source is `407be551594026dc2e16a2be179f0682bfbe88aa`. The selected route is
`backend_helpers` → `cranelift_compile_module_direct` → the codegen SFFI
`rt_cranelift_new_aot_module_triple` / configured-v2 constructor. It is the
Cranelift 0.116.1 Rust provider, not the separate native register allocator.

The retained relink manifest binds `simple_native_all.lib` at SHA-256
`95b51653e802b2998a520c04250cef990e4df6fb868d16126c1d15e50466d7b6`.
Replacing only Pure Simple objects cannot update that linked provider.

## Repair

Both common and configured-v2 ISA construction apply one target policy:
x86-64 Windows enables inline stack probes with a 4 KiB guard size. Setting
failure rejects ISA creation. Other target policies are unchanged. Inline
probing avoids introducing an unprovided outline probe libcall.

Cranelift 0.116.1's x64 implementation supports both System V and Windows
Fastcall: it touches each guard interval and restores RSP before ordinary
frame allocation. Its large-frame loop uses caller-saved r11, which is not an
argument register. No custom register-save or stack-layout implementation is
introduced here.

Microsoft's [x64 prolog contract](https://learn.microsoft.com/en-us/cpp/build/prolog-and-epilog?view=msvc-170)
requires probing large fixed stack allocations before using their storage.

## Actual evidence

Evidence root: `runtime/windows-restart-20261004` in the session runtime tree.

* `win64-stack-probe-cycle1`: exact production policy/ISA function bodies were
  extracted with SHA-256 pins into a minimal offline Cargo harness, using
  Cranelift `=0.116.1` and target-lexicon `=0.13.4`. Three tests passed: Windows
  and unchanged Linux/macOS policy; generated machine-code probes for eight
  frame sizes (16 through 1 MiB, including 58,528); fresh Windows thread
  execution for five frame sizes, each returning 84 after first/last local
  stores. Generated code has no probe relocations. The harness does not
  substitute for compiling the full SFFI module/registry constructor test.
* Actual watchdog: complete, exit 0, peak RSS 1,019,216 KiB,
  observer_errors=0, quiescent=1. Cargo and test requested workers: 80.
* `win64-stack-probe-baseline`: the same fresh-thread test with the original
  `918498b2b185a4026c4313bc7ba0cea774f107a4` ISA constructor, extracted unchanged,
  terminates with `0xc0000005`. Watchdog exit 139, peak RSS 459,284 KiB,
  observer_errors=0, quiescent=1. This demonstrates the unprobed-frame failure
  mechanism without debugger attachment or exception dumps.

Initial harness setup errors (host text encoding, setup root/TMP requirements)
occurred before native execution and are retained separately. No successful
criterion was rerun. Neither old source nor old archives were overwritten.

## Required integration validation

On an isolated full source containing this fix, with the canonical MSVC/SDK
environment and an owned compatible Cargo cache, run the focused provider test:

```sh
cargo test --offline --release -p simple-compiler --lib --features llvm win64_stack_probe_ --jobs 80 -- --nocapture --test-threads=80
```

Then build the same provider feature union used by the retained producer:

```sh
cargo build --offline --release -p simple-driver --bin simple --lib -p simple-native-all --features simple-native-all/driver-compat,simple-driver/llvm --jobs 80
```

Both commands require the canonical process-tree owner and actual memory
admission. Export new immutable producer/archive hashes; do not overwrite the
old tuple. Relink/rebuild the next producer with that archive under fresh
source/runtime authority, then recompile and execute the original scalar
fixture and inspect its retained prologue. Full constructor tests, original
fixture repair, self-hosted compiler/core/MCP tests and bootstrap qualification
are **UNRUN**, not inferred from this focused harness.
