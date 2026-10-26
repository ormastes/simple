# Captured Rust API diagnostic omitted runtime C build inputs

Status: OPEN_CAPTURE_LIMITATION_SOURCE_ESTABLISHED; final execution failed before tests.

The isolated source-authority diagnostic snapshot was prepared with one-off
orchestration that captured owned Rust crates, path dependencies and literal
includes. It was not a canonical production closure capturer. It omitted all27
Windows-selected C files computed by src/compiler_rust/runtime/build.rs. The
snapshot src/runtime tree contains hosted/ only; the actual current C files exist.

The actual build script adds files only when they exist and then calls
build.compile("runtime_sffi_c"). With zero selected objects, cc-rs dispatches no
archive command and later attempts MSVC publication from an absent archive.
Final locked test execution ended Cargo101 after768.32seconds, no tests ran,
postflight pins unchanged, finalJob0, peakRSS1051104KiB. A matching manifest
therefore established immutability of an incomplete closure, not completeness.

The generic cc-rs message discards underlying filesystem errors. No path-length,
permission, LLVM tool-version or disk failure is established by that message.
This capture limitation does not prove a deployed compiler/runtime regression.

Required repair: compute target-specific build-script C inputs and recursive
header/generated-input dependencies, pin them in a new explicit capture, and
fail admission when any required input is absent before expensive compilation.
Do not silently drop --locked, use live ambient sources, produce an empty archive,
or rewrite original failed snapshots/receipts to claim a pass. The existing
three-cycle execution budget is exhausted; no fourth automatic retry.

Evidence: provider-isolation-execution-cycle3-locked-tests/result.json and
artifacts/output.log; ASTRA_RUNTIME_BUILD_INPUT_AUDIT.json;
cargo-runtime-library-publication-static-20261011/REPORT.json.
Bug database reconciliation pending. Pure authority, performance and Phase3
remain unqualified; no GitHub landing.