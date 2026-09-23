# macOS Phase2 core-C linker symbols (group 1)

Status: draft source fix, not a full Phase2 admission. Source branch starts at
`eef513cb596ccf15c815f63ac0e2e818d713ea34`; failing bootstrap evidence
used source `70748fd0a165e5a82f44f91dba839b21a35a0ce9`.

## Reproducer and scope

The retained `compiler_cli_build.log` at
`/Users/ormastes/simple-tmp/macos-bootstrap-restore-20260923/build/evidence/cache-loss-70748fd0/phase2/logs/`
reports missing `stderr_write`, `stderr_flush`, `rt_numeric_sum_f64`,
`rt_array_sorted`, and `rt_gui_present_html` among other independent linker
groups. The host-GPU CLI links the core-C runtime; a symbol existing in the
hosted Rust runtime does not provide it to that C-owned value ABI. This change
only addresses these five names; it does not claim the full CLI now links.

Trace32 logging now calls the existing core-C `rt_stderr_write`/`flush` ABI.
Core-C implements non-allocating scalar numeric sum and representation-aware
sorted-copy array parity. Packed byte/u64 slots are sorted as raw scalars;
generic tagged slots use a stable O(n log n) merge with the hosted Rust
sorted-copy ordering (tagged ints before floats, unsigned boxes by value,
otherwise stable Equal) rather than the existing `rt_sort` insertion sort's
O(n²) interpreter ordering. The HTML GUI symbol is a small optional dynamic-library bridge, not
an eager AppKit dependency. It reads `SIMPLE_GUI_HTML_PROVIDER_PATH` on first
use only and requires an absolute path to a library exporting
`simple_gui_html_provider_abi_v1` and `simple_gui_present_html_v1`. The
version must be 1. The library receives borrowed UTF-8 bytes for the call
only and must return 1 after accepting the frame; all unavailable/rejected
cases exit 70 with a fixed diagnostic. The handle is cached for process
lifetime; this deliberately bounds loading to one provider per process and
avoids per-frame filesystem scans or `dlopen`. No production HTML provider
is shipped by this patch, so actual HTML GUI presentation remains unavailable
until a compatible optional library is installed/configured. A test fixture
is not a production provider.

## Focused evidence and limits

Reproduce the isolated native probe from the repository root on macOS:

```sh
mkdir -p build/native_probe
clang -c -O0 -ffunction-sections -fdata-sections -std=gnu11 -DSIMPLE_CORE_C_STANDALONE=1 -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o build/native_probe/runtime_native_sections.o
clang -Wl,-dead_strip -std=gnu11 -Isrc/runtime -Isrc/runtime/platform src/runtime/test/rt_core_c_utf8_math_array_twin_parity_selfcheck.c build/native_probe/runtime_native_sections.o -lpthread -lm -o build/native_probe/core_c_parity_selfcheck
build/native_probe/core_c_parity_selfcheck
clang -Wl,-dead_strip -std=gnu11 -Isrc/runtime -Isrc/runtime/platform src/runtime/test/rt_gui_html_dynload_selfcheck.c build/native_probe/runtime_native_sections.o -lpthread -lm -o build/native_probe/gui_html_dynload_selfcheck
clang -dynamiclib -std=gnu11 -Isrc/runtime src/runtime/test/rt_gui_html_provider_fixture.c -o build/native_probe/libsimple_gui_html_test_v1.dylib
env SIMPLE_GUI_HTML_PROVIDER_PATH="$PWD/build/native_probe/libsimple_gui_html_test_v1.dylib" build/native_probe/gui_html_dynload_selfcheck present
```

For failure branches, rerun the fixture compilation with
`-DSIMPLE_GUI_TEST_ABI_VERSION=2` or `-DSIMPLE_GUI_TEST_REJECT_FRAME=1`,
and call the driver with an unset/nonexistent provider path or `invalid-tag`.
The driver returns 0 only for accepted frames; refusal must be exit 70.
The reentry fixture is compiled with `-DSIMPLE_GUI_TEST_REENTER=1`; link its
driver with `-Wl,-exported_symbol,_rt_string_new` and
`-Wl,-exported_symbol,_rt_gui_present_html` so `dlsym(RTLD_DEFAULT, ...)`
can call back during the version handshake. With the event lifecycle
integration, the outer callback guard exits 70 with `GUI callback reentry`
before entering the preserved initialization guard.

On macOS, the sectioned standalone `runtime_native.c` compiled and linked
with the C selfchecks. `rt_core_c_utf8_math_array_twin_parity_selfcheck`
passed 123 checks including sum, invalid input, packed byte/u64 sorted-copy,
mixed int/float and unsigned ordering, stable text relative order, and
original array preservation. The HTML test fixture passed a valid provider with one
version lookup/two frame calls; absent path, nonexistent library, ABI version
2, rejected frame, invalid tagged text, and provider-version callback reentry
each exited 70 with the expected
reason. This is
source/isolated-native evidence only. Full source-matched Phase2 CLI relink,
compiler tests, and production HTML rendering are pending, as are other
linker-symbol groups owned separately.

The runtime-owned bridge uses `getenv` only in C runtime initialization;
there are no new app-leaf direct environment reads. The provider receives no
owned copy of HTML and must not retain the pointer. Runtime shutdown retains
one dynamic-library handle to avoid invalidating the cached function pointer.
The provider's version callback must not reenter the HTML runtime entrypoint;
present calls can be concurrent and the provider must handle GUI-thread
routing or serialization. The bridge refuses same-thread initialization
reentry and yields while another thread completes the one-time load.
The wait is one-time and cooperative, not a hard timeout against a provider
that stalls inside `dlopen` or its version callback.

The source-list parity gate remains red independently: its committed-tree
check (`--rev HEAD`) finds the previously tracked
`test/rt_windows_file_publish_selfcheck.c` absent from the frozen baseline.
The two new GUI fixture C files are listed as `none` in this patch; the
unrelated existing baseline drift is not claimed fixed here.
