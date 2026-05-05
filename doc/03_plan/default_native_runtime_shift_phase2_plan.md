# Default Native Runtime Shift - Phase 2 Plan

## Context

Phase 1 is complete:

- native runtime lanes are explicit: `simple-core`, `core-c-bootstrap`, `rust-hosted`
- non-compiler `auto` no longer silently falls back to `rust-hosted`
- launcher, wrapper, and packaging surfaces now treat hosted/source-entry execution as explicit legacy fallback

What remains is the runtime and service port work that makes the new default lane real for the current hosted-heavy app surfaces.

This plan covers the remaining three items:

1. implement the `simple-core` ABI/runtime
2. migrate MCP/LSP off `rust-hosted`
3. package MCP/LSP binaries on a core lane instead of explicit hosted packaging

Related docs:

- `doc/04_architecture/default_native_runtime_shift_to_c_core_abi.md`
- `doc/05_design/default_native_runtime_shift_to_c_core_abi.md`

## Goals

- Make `simple-core` a real, testable, selectable runtime lane rather than an archive-presence alias.
- Preserve MCP/LSP behavior while removing implicit or primary-lane dependence on `libsimple_native_all.a`.
- End with packaged MCP/LSP binaries that build and run on a core lane by default.

## Non-Goals

- Migrating compiler/bootstrap/self-host flows off `rust-hosted`.
- Reworking MCP protocol shape, tool inventory, or client-facing behavior to make the port easier.
- Broad hosted-runtime decomposition beyond what is needed for hello, standalone TUI, MCP, and simple LSP MCP.

## Exit Criteria

- `simple-core` links and runs `hello` and standalone TUI without `libsimple_native_all.a`.
- MCP and simple LSP MCP pass startup and smoke protocol checks on a core lane.
- package build commands for MCP/LSP no longer require `--runtime-bundle rust-hosted`.
- selected core lanes contain no unwind dependency and no hosted-runtime archive in their closure.

## Workstream 1: Implement `simple-core` ABI/Runtime

### Objective

Create a pure-Simple implementation of the narrow host ABI already defined by the phase-1 lane contract, with behavior matched against the C bootstrap lane.

### Current State

- `simple-core` is selectable in native-build policy.
- the lane is still effectively a placeholder around archive discovery and guardrails.
- `src/runtime/libsimple_runtime.a` remains the active narrow-lane implementation root.

### Deliverables

- a concrete `simple-core` runtime archive/module tree
- a shared ABI conformance suite that runs against `core-c-bootstrap` and `simple-core`
- lane selection logic that prefers `simple-core` based on ABI completeness, not only archive presence

### Required ABI Surface

- startup/shutdown
- argv install/read
- text creation/access helpers required by generated code
- stdout/stderr write and flush
- alloc/free/realloc/memcpy/memset
- exit/time/sleep
- minimal array/value helpers still required by current codegen
- panic-abort behavior only, with no unwind across the ABI

### Planned Steps

1. Freeze the ABI inventory in one machine-readable location.
   Candidate touch points:
   - `src/compiler_rust/runtime_abi`
   - `src/compiler_rust/runtime`
   - `src/runtime/runtime.h`
   Output:
   - one authoritative symbol list grouped by family
   - classification for each symbol: `core-required`, `hosted-only`, `unported`

2. Build a conformance harness before the Simple port grows.
   Candidate coverage:
   - argv round-trip
   - stdout/stderr writes and flush ordering
   - allocation/reallocation semantics
   - monotonic or wall-clock time contract used by current stdlib calls
   - abort semantics for panic/fatal runtime errors
   Verification shape:
   - one test matrix that runs the same host ABI checks against both `core-c-bootstrap` and `simple-core`

3. Split `simple-core` into ABI families rather than one monolith.
   Proposed implementation families:
   - startup/args
   - text/value
   - io/print
   - memory
   - time/process basics
   Constraint:
   - keep object or archive granularity small enough for dead-strip to work for `hello`

4. Teach lane resolution to check ABI completeness.
   Current behavior:
   - `auto` prefers `simple-core` when the archive exists
   Target behavior:
   - `auto` prefers `simple-core` only when all `core-required` symbols for the target class are implemented
   Candidate touch points:
   - `src/compiler_rust/compiler/src/pipeline/native_project/config.rs`
   - `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`
   - related unit tests in `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs`

5. Move `hello` and standalone TUI to verified `simple-core`.
   Constraints:
   - no `libsimple_native_all.a`
   - no libunwind retention
   - no hosted-only extern leakage

### Risks

- generated code may still depend on helper symbols not currently classified as core ABI
- text/value helpers may be entangled with broader runtime objects and need archive splitting first
- TUI may expose missing terminal or process primitives that belong in the shared core ABI

### Verification

- existing runtime-bundle Rust tests plus new ABI-completeness tests
- `hello` build and run on `core-c-bootstrap`
- `hello` build and run on `simple-core`
- standalone TUI build and run on `core-c-bootstrap`
- standalone TUI build and run on `simple-core`
- closure audit scripts show no `libsimple_native_all.a` or unwind artifacts

### Progress 2026-05-04

- ABI inventory and classification started in `src/compiler_rust/common/src/runtime_symbols.rs`, re-exported through `simple-common` and `simple-runtime-abi`.
- Lane resolution now only auto-selects `simple-core` when the archive exports all `core-required` symbols; incomplete placeholder archives fall back to `core-c-bootstrap`.
- Core-C bootstrap archive construction no longer depends on process cwd and is covered by the native-project tests.
- Initial conformance gate added: `test_core_lane_runtime_archives_expose_required_abi_symbols` verifies the generated core-C archive, and any discovered `simple-core` archive, against the authoritative required-symbol list.
- Core-C runtime now exports the missing required stdout/stderr and value-constructor ABI symbols needed for that gate.
- Core-required ABI now includes the framed-stdio startup symbols `stdin_read_char` and `print_raw`; the core-C behavior probe covers stdin byte read, raw stdout write, stdout/stderr flush, and value constructors.
- `scripts/check-simple-core-runtime-smoke.shs` now materializes `build/simple-core/libsimple_runtime.a` from the core C runtime sources, verifies required ABI exports including `rt_platform_name`, and runs explicit `--runtime-bundle simple-core` smoke checks. This is a reproducible ABI-complete bootstrap gate, not the final pure-Simple core family implementation.
- `hello_native.spl` builds and runs on explicit `simple-core`, producing `Hello World`; the smoke script audits the hello and TUI smoke binaries for `libsimple_native_all.a`, `rust-hosted`, and unwind markers.
- The generated standalone TUI wrapper and the real `run_tui("examples/ui/minimal.ui.sdn")` app path both build and run on explicit `simple-core`, exit 0, and print `UI closed.`. The real app path renders through `screen_render(screen)` and exits cleanly on stdin EOF in native smoke mode.
- Core C runtime now matches the compiled Simple array ABI for `rt_array_push`, `rt_array_get`, `rt_array_set`, `rt_index_get`, `rt_index_set`, and generic `rt_len` on arrays; a native `[text]` push/len/index probe on explicit `simple-core` returns `1` and `abc`.
- Native-project archive output support now exists for Simple objects through `NativeBuildConfig.emit_archive`; `test_native_project_emit_archive_writes_static_archive` verifies that a Simple source file can be archived into `libsimple_runtime.a` with an exported symbol.
- The required-ABI behavior probe is now shared by `core-c-bootstrap` and any discovered ABI-complete `simple-core` archive: `test_core_lane_runtime_required_abi_stdout_stderr_and_values` links the same C probe against both lanes and checks stdin byte read, raw stdout write, stdout/stderr flush, and value constructors.
- The archive-output regression now also verifies that Simple source objects can preserve runtime-style exports (`rt_*` and `__simple_*`), so the next blocker is implementation of the required symbols and host-primitive boundary rather than native symbol spelling.
- A Simple-source `simple-core` module tree exists at `src/runtime/simple_core/`; `test_simple_core_source_tree_emits_partial_runtime_archive` builds it as a `no_mangle` archive, requires all 41 core-required symbols, and validates value, memory, process, array, string, equality, slice, conversion, and string-backed stdio behavior without linking the C runtime archive.
- Cranelift/common backend runtime declarations now allow a module to define a body for a known runtime FFI name instead of always treating that name as an import; `rt_value_float` and `rt_value_bool` runtime FFI metadata now matches the C/core ABI `int64_t` signatures from `src/runtime/runtime.h`.
- The Simple-source `simple-core` tree now owns the memory ABI family (`rt_alloc`, `rt_realloc`, `rt_free`, `rt_memcpy`, `rt_memset`) via explicit libc host-primitive wrappers in `src/runtime/simple_core/core_memory.spl`; the partial archive behavior probe links without the C runtime archive and validates tagged-value plus memory operations.
- The Simple-source `simple-core` tree now owns process/time/panic symbols (`rt_exit`, `rt_time_now_unix`, `rt_sleep_ms`, `rt_panic`) through `src/runtime/simple_core/core_process.spl`; runtime FFI metadata and `runtime.h` now expose matching core ABI declarations, and the partial archive behavior probe validates `rt_time_now_unix` plus `rt_sleep_ms(0)`.
- The Simple-source tree now owns the layout-independent stdio flush symbols (`rt_stdout_flush`, `rt_stderr_flush`) through `src/runtime/simple_core/core_stdio.spl`, using libc `fflush(NULL)` while string-backed stdin/stdout/stderr byte transfer remains blocked on heap text layout access from Simple.
- Native codegen now lowers Simple runtime-internal memory intrinsics (`spl_load_i64`, `spl_store_i64`, `spl_load_u8`, `spl_store_u8`) directly to native loads/stores; `test_simple_runtime_memory_intrinsics_lower_without_helper_symbols` verifies they do not leak helper symbols into archives.
- The Simple-source tree now owns the array ABI family (`rt_array_new`, `rt_array_len`, `rt_array_get`, `rt_array_set`, `rt_array_push`, `rt_array_pop`) through `src/runtime/simple_core/core_array.spl`; the partial archive behavior probe validates push, len, get, tagged-index get, set, pop, growth, and out-of-range nil behavior without linking the C runtime archive.
- The Simple-source tree now owns the remaining string, generic length/conversion/slice/equality, stdin byte-read, raw stdout/stderr write, and print aliases through `src/runtime/simple_core/core_string.spl`.
- `scripts/check-simple-core-runtime-smoke.shs` now builds `build/simple-core/libsimple_runtime.a` from `src/runtime/simple_core` with `--emit-archive --no-mangle` (falling back to the current Rust CLI if `bin/simple` is stale), then verifies hello, standalone TUI, interactive TUI, and closure cleanliness on the selectable `simple-core` lane.
- Pure-Simple source coverage is now 41 of 41 `core-required` symbols.

## Workstream 2: Migrate MCP/LSP Off `rust-hosted`

### Objective

Port the runtime and service dependencies used by `src/app/mcp` and `src/app/simple_lsp_mcp` into the shared core lane without shrinking protocol behavior.

### Current State

- launchers and docs already treat hosted execution as explicit legacy fallback
- package-shape MCP/LSP builds now use the default core-lane policy without `--runtime-bundle rust-hosted`
- MCP and Simple LSP MCP startup plus `tools/list` are available on the core lane; broader hosted-only tool behavior remains classified outside this phase

### Deliverables

- an audited dependency map from MCP/LSP entrypoints to runtime symbols and hosted subsystems
- core-lane replacements for the MCP/LSP-critical services
- explicit classification for any still-hosted-only feature path

### Dependency Layers To Port

1. stdio transport
2. JSON/text helpers
3. process/env/file helpers
4. command execution and passthrough support
5. task/session helpers used by current server startup and request handling

### Planned Steps

1. Build a dependency inventory from the live entrypoints.
   Primary entrypoints:
   - `src/app/mcp/main.spl`
   - `src/app/simple_lsp_mcp/main.spl`
   Important adjacent modules:
   - `src/app/mcp/main_dispatch.spl`
   - `src/app/mcp/tool_registry.spl`
   - `src/app/mcp/startup_log.spl`
   - `src/app/simple_lsp_mcp/protocol.spl`
   - `src/app/simple_lsp_mcp/tools.spl`
   Output:
   - grouped map of runtime externs and stdlib facilities used at startup
   - grouped map of runtime externs and stdlib facilities used on hot request paths

2. Separate startup-critical dependencies from tool-only dependencies.
   Reason:
   - startup must move first to achieve native server health checks and packaging
   - tool-only features can fail clearly if still unported, as long as they are classified explicitly

3. Port MCP/LSP core services into shared core-lane modules.
   Priority order:
   - framed stdio IO
   - JSON parsing/serialization needed by initialize and tools/list
   - basic file/env/process utilities used by registry and workspace tools
   - command execution support used by passthrough and helper tools
   - session/task support only where required for existing request paths
   Constraint:
   - new helpers should land in shared runtime or shared stdlib layers, not app-local one-offs

4. Add explicit hosted-only boundaries where parity is not finished.
   Required behavior:
   - fail with a clear error naming the hosted-only capability
   - do not route the whole server back to `rust-hosted`

5. Switch default MCP/LSP core-lane smoke tests to run without hosted packaging.
   Existing verification anchors:
   - `test/system/mcp/mcp_startup_test_system.shs`
   - `test/system/mcp/mcp_lifecycle_test_system.shs`
   - `test/integration/app/mcp_stdio_integration_spec.spl`

### Risks

- tool inventory breadth in `src/app/mcp` may hide hosted dependencies behind rarely-used tools
- process execution and shell passthrough may drag in broader hosted runtime surfaces if not split carefully
- simple LSP MCP tool-runner and daemon paths may need separate classification from base protocol startup

### Verification

- `initialize` and `tools/list` green on a core lane
- current MCP smoke tests remain green without hosted runtime in the package closure
- explicit hosted-only tool paths fail with intentional diagnostics, not implicit fallback
- startup time and RSS do not regress materially relative to current package expectations

### Progress 2026-05-04

- Dependency inventory written to `doc/03_plan/default_native_runtime_shift_mcp_lsp_dependency_inventory.md`.
- Inventory separates startup-critical dependencies from hot request path and tool-only dependencies.
- Startup-critical groups identified: framed stdio, raw stdout response writes, pure Simple JSON helpers, `rt_exit`, startup diagnostics, and static tools/list schema generation.
- Tool-only or later-port groups identified: file/env workspace helpers, process execution, async process/session control, time helpers, and TRACE32/dialog passthrough.
- First framed-stdio core-C ABI pieces are covered by `test_core_c_runtime_required_abi_stdout_stderr_and_values`; remaining startup work is Simple-side protocol smoke on a core lane.
- Core-lane MCP/LSP build probes recorded in the inventory: full Simple LSP MCP and full MCP now link on `core-c`, but both still generate internal Simple stubs and therefore are not package-closure PASS gates yet.
- Full Simple LSP MCP now answers a two-message framed initialize + tools/list smoke on `core-c` with real LSP tool schemas. Full MCP answers JSON-lines initialize + tools/list without crashing, but tools/list is still empty because the large tool-table accumulation path remains unsafe on the core lane.
- Reduced-source Simple LSP MCP startup is covered by `test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source`.

### Progress 2026-05-05

- Full MCP and Simple LSP MCP package-shape binaries build without `--runtime-bundle rust-hosted` using the default core-lane policy.
- MCP JSON-lines `tools/list` returns 144 tools with valid schemas; Simple LSP MCP framed `tools/list` returns 11 tools with valid schemas.
- The pure-Simple `simple-core` archive now supplies the framed stdio and string/array/value ABI needed by the startup and tools/list paths; hosted remains an explicit compatibility lane for broader tool behavior outside this phase.

## Workstream 3: Package MCP/LSP Binaries On Core Lanes

### Objective

Remove the temporary explicit hosted packaging commands and ship MCP/LSP artifacts through the same core-lane policy model now used by default runtime selection.

### Current State

- MCP/LSP package docs now use core-C package build commands instead of explicit `rust-hosted` commands.
- registry launchers and wrappers already expect wrapper/native-first distribution

### Deliverables

- package build commands for `simple_mcp_server` and `simple_lsp_mcp_server` that succeed on a core lane
- package validation that asserts no hosted archive is linked in the shipping artifact
- updated docs and release checks that no longer mention explicit hosted packaging for these servers

### Planned Steps

1. Make package build lane selection explicit during migration.
   Interim target:
   - package scripts choose `simple-core` first, `core-c-bootstrap` only when explicitly configured for bootstrap verification
   - never default packages back to `rust-hosted`

2. Add package closure validation.
   Required checks:
   - no `libsimple_native_all.a`
   - no unwind dependency
   - expected wrapper/native assets exist after packaging

3. Update package smoke flows and registry verification.
   Candidate surfaces:
   - MCP/LSP package build docs
   - registry postinstall expectations
   - wrapper health checks
   - any publish-time smoke scripts for npm and registry bundles

4. Promote core-lane packaging to the documented default.
   Remove temporary notes once both servers ship on the core lane.

### Risks

- package build may succeed while a subset of tools still rely on runtime/source fallback
- wrapper/native assets may drift from the package closure checks unless the package validation is made mandatory

### Verification

- native-build package commands succeed without `--runtime-bundle rust-hosted`
- packaged binaries respond to `initialize` and `tools/list`
- package closure audit confirms no hosted runtime artifacts
- npm or registry wrapper smoke remains green with downloaded package contents

### Progress 2026-05-04

- Package-shape app-only builds now succeed on `core-c`:
  - `bin/simple native-build --runtime-bundle core-c --source src/app --entry-closure --entry src/app/mcp/main.spl --strip --output /tmp/simple_mcp_core_c_app_probe`
  - `bin/simple native-build --runtime-bundle core-c --source src/app --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output /tmp/simple_lsp_mcp_core_c_app_probe`
- App-only MCP and Simple LSP MCP binaries pass initialize + tools/list smoke on `core-c`; MCP includes `debug_create_session`, `simple_check`, and `test_daemon_status`, and Simple LSP MCP includes `lsp_definition`.
- Closure audit on those app-only core-C binaries found no `libsimple_native_all.a`, `rust-hosted`, or unwind strings/symbols.
- `doc/07_guide/tooling/mcp.md` now documents core-C package validation commands for MCP/LSP instead of `rust-hosted`.
- `scripts/check-mcp-native-smoke.shs` now validates the mixed transports used by the package binaries: MCP JSON-lines and Simple LSP MCP framed `Content-Length`. The package smoke reports 144 MCP tools and 11 LSP tools with valid schemas.

### Progress 2026-05-05

- Native package-shape build commands for MCP and Simple LSP MCP pass without explicit hosted runtime selection:
  - `bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output <tmp>/simple_mcp_server`
  - `bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output <tmp>/simple_lsp_mcp_server`
- The resulting binaries pass `tools/list` smoke with 144 MCP tools and 11 LSP tools, and both schema sets validate.

## Sequencing

### Milestone A: ABI Freeze And Conformance

- freeze symbol inventory
- build conformance suite
- classify hosted-only vs core-required symbols

### Milestone B: `simple-core` For Hello/TUI

- implement pure-Simple core families
- prove `hello` and standalone TUI on `simple-core`
- keep `core-c-bootstrap` as compatibility floor

### Milestone C: MCP/LSP Startup Port

- port stdio, JSON, and process/env/file minimums
- get `initialize` and `tools/list` green on a core lane

### Milestone D: MCP/LSP Tool Parity

- port remaining hot-path services
- classify or eliminate remaining hosted-only tool paths

### Milestone E: Core-Lane Packaging

- remove explicit hosted package build requirement
- promote package validation and release docs

## Suggested Verification Order

1. Rust runtime-bundle and native-project unit tests
2. hello-world lane checks
3. standalone TUI closure and size checks
4. MCP startup and lifecycle smoke on a core lane
5. native package build and wrapper smoke

## Definition Of Done

- `simple-core` is chosen because it is ABI-complete, not because a placeholder archive exists
- `hello`, standalone TUI, simple MCP, and simple LSP MCP all run on a core lane
- package build instructions no longer mention `--runtime-bundle rust-hosted` for MCP/LSP
- hosted remains available only as an explicit compatibility lane for flows not yet migrated
