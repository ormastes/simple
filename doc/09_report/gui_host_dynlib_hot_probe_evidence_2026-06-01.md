# GUI Host Dynlib Hot Probe Evidence

Date: 2026-06-01

## Scope

Diagnostic evidence for the pure GUI hot symbol as a callable host dynamic
library. This is not SMF acceptance evidence.

## Build

```bash
mkdir -p build/gui
SIMPLE_LIB=src src/compiler_rust/target/debug/simple compile src/app/gui_perf/pure_gui_hot_dynlib_export.spl --native --shared --strip -o build/gui/libpure_gui_hot.so
```

Result:

```text
Compiled src/app/gui_perf/pure_gui_hot_dynlib_export.spl -> build/gui/libpure_gui_hot.so (5891832 bytes, opt-level=aggressive)
```

## Probe

```bash
SIMPLE_LIB=src SIMPLE_GUI_DYNLIB_ARTIFACT=build/gui/libpure_gui_hot.so src/compiler_rust/target/debug/simple run src/app/gui_perf/smf_dynlib_probe.spl
```

Result:

```text
GUI_DYNLIB_PERF artifact=build/gui/libpure_gui_hot.so loader=host_dynlib symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 warmup=16 p50_us=17 p95_us=19 p99_us=26 max_us=27 threshold_us=1000 pass=false error=not-smf-dynlib
```

## Interpretation

The pure GUI i64 hot symbol is callable through a real host dynlib and is well
below the 1000 us p99 target. The row correctly fails because the requested
acceptance loader is `smf_dynlib`, not `host_dynlib`.

## SMF-Wrapped Host Dynlib Evidence

After adding the role-2 SMF wrapper/extractor path, the current Linux host can
wrap the same pure GUI shared library into an SMF envelope and measure the hot
symbol from the SMF artifact:

```bash
SIMPLE_LIB=src src/compiler_rust/target/debug/simple compile src/app/gui_perf/smf_wrap_host_dynlib.spl --native --strip -o build/gui/smf_wrap_host_dynlib
SIMPLE_LIB=src src/compiler_rust/target/debug/simple compile src/app/gui_perf/smf_dynlib_probe.spl --native --strip -o build/gui/smf_dynlib_probe
SIMPLE_GUI_DYNLIB_INPUT=build/gui/libpure_gui_hot.so SIMPLE_GUI_SMF_OUTPUT=build/gui/pure_gui_hot.smf ./build/gui/smf_wrap_host_dynlib
SIMPLE_GUI_DYNLIB_ARTIFACT=build/gui/pure_gui_hot.smf ./build/gui/smf_dynlib_probe
```

Result:

```text
GUI_SMF_WRAP ok=true input=build/gui/libpure_gui_hot.so output=build/gui/pure_gui_hot.smf
GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf loader=smf_dynlib symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 warmup=16 p50_us=1 p95_us=1 p99_us=1 max_us=1 threshold_us=1000 pass=true error=
```

This is real SMF artifact evidence on the Linux host: the probe extracts the
role-2 native library stub from the SMF envelope outside the measured loop,
opens the extracted dynlib once, resolves the symbol, and times direct symbol
calls. The remaining acceptance evidence still needs the same row from a macOS
arm64 `.dylib` wrapped in SMF.

## SimpleOS Dynload Support

The SimpleOS kernel dynload registry now accepts role-2 SMF library envelopes
as first-class dynamic-library inputs. `dylib_registry_register()` unwraps the
native library stub from SMF, validates it as ELF for SimpleOS symbol lookup,
and `dylib_registry_symbol()` resolves `.dynsym` names from that payload.

Focused evidence:

```bash
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/os/kernel/loader/dylib_registry.spl test/01_unit/os/kernel/loader/dylib_registry_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/os/kernel/loader/loader_api.spl src/os/kernel/loader/dylib_registry.spl src/os/kernel/ipc/syscall_process.spl test/01_unit/os/kernel/loader/loader_api_spec.spl test/01_unit/os/kernel/loader/dylib_registry_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/loader/loader_api_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/loader/dylib_registry_spec.spl --mode=interpreter --clean --format json
```

Result: `loader_api_spec` passed 5/5 and `dylib_registry_spec` passed 7/7,
including role-2 SMF library dynload symbol resolution. The registry still
reports these symbols as not process-callable because SimpleOS has not yet
mapped the shared object into the current process with executable permissions.
The broader `syscall_spec` timed out after 120 seconds in interpreter mode
before listing scenarios; the syscall bridge typecheck passed in the focused
check above.

## macOS Arm64 Evidence Runner

The macOS evidence runner is now implemented in Simple:

```bash
SIMPLE_LIB=src src/compiler_rust/target/debug/simple run src/app/gui_perf/macos_smf_dynlib_evidence.spl
```

On non-macOS hosts it emits an explicit skip row:

```text
GUI_MAC_SMF_DYNLIB_EVIDENCE status=skip host_os=linux arch=x86_64 reason=requires-macos-arm64
```

On macOS arm64 the same runner compiles the pure Simple GUI hot symbol as a
`.dylib`, compiles the SMF wrapper and probe as native executables, wraps the
`.dylib` into a role-2 SMF artifact, runs the probe, and accepts only a
`GUI_DYNLIB_PERF` row with `loader=smf_dynlib`,
`call_source=dynlib_symbol_call`, and `pass=true`.

Focused evidence:

```bash
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/app/gui_perf/macos_smf_dynlib_evidence_core.spl src/app/gui_perf/macos_smf_dynlib_evidence.spl test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/app/gui_perf/macos_smf_dynlib_evidence_spec.spl --mode=interpreter --clean --format json
```

Result: `macos_smf_dynlib_evidence_spec` passed 5/5. This Linux run does not
claim macOS arm64 acceptance; it only proves the runner gates and policy.
