# A native shared library built under `SIMPLE_MCDC_MODE=on` cannot be dlopen'd (2026-11-13)

Status: open. Worked around in `scripts/check/check-xray-native-program-e2e.shs`
(the module build runs with the MC/DC variables unset).

## Symptom
The seed's spec runner exports `SIMPLE_MCDC_MODE=on` to every child process.
`compile --native --backend=native --xray` of `test/fixtures/xray/xray_inprocess_prog.spl`
(shared-library intent, pinned seed 554460a6b85a, aarch64) then succeeds
(`CLI-COMPILE rc=0`) but the module carries undefined references:

    U lib.nogc_sync_mut.mcdc.static_probe.mcdc_static_probe_begin
    U lib.nogc_sync_mut.mcdc.static_probe.mcdc_static_probe_condition
    U lib.nogc_sync_mut.mcdc.static_probe.mcdc_static_probe_end

`dlopen(RTLD_NOW)` refuses it, so `XrayNativeDlModuleV1.open` returns
`InvalidArgument` (status 10). The same build without the variable is
byte-stable (sha256 `9591d21aee45…`) and loads.

## Repro
    SIMPLE_MCDC_MODE=on XR_SRC=test/fixtures/xray/xray_inprocess_prog.spl XR_OUT=/tmp/libon.so XR_XRAY=1 \
      SIMPLE_NATIVE_BUILD_EMIT_OBJECT=shared <seed> run test/fixtures/xray/xray_native_cli_compile_driver.spl
    llvm-nm -D -u /tmp/libon.so | grep mcdc

## Expected
Either the probe runtime is linked into an MC/DC-instrumented shared object,
or a native build that cannot carry the probe runtime refuses MC/DC mode with a
diagnostic. Emitting unresolved probe calls is fail-open at build time and
fail-closed only at load time.

## Impact
Any spec that builds a native shared library through a child process
(`check-xray-native-inprocess-e2e.shs`, the program lane) fails under the spec
runner while the same script passes from a shell.
