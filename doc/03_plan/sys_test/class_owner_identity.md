# P3 verification plan

The unit specification is test/unit/compiler/hir/class_owner_identity_spec.spl.
It checks qualified IDs and aliases, Windows/dotted owner equivalence, nested
Named relocation under numeric collisions, default-helper/capture relocation,
explicit-versus-omitted default behavior, two provider layouts, and ABI names.

The native fixture entry is
test/fixtures/compiler/class_owner_identity/src/identity/main.spl. Compile its
src root with entry closure enabled, execute the produced program, and inspect
the emitted definitions/calls for provider-owned methods/helper main and bare
ABI guards. Repeat the runtime array push assertion on Windows and another
supported host before claiming cross-host acceptance.

Required self-hosted gates remain compiler/lib/MCP/LSP checks, MCP stdio
integration, core runtime smoke, and MCP native smoke. Run the source env/process
guards and spec-layout gate independently of runtime availability.

Measure metadata preparation and representative qualified lookup elapsed time
and peak RSS using the admitted runtime. Do not report a Python model or the
Rust bootstrap seed as evidence for those performance requirements.

Execution status is recorded in doc/09_report/class_owner_identity_2026-09-22.md.

## Open acceptance TODO (runtime owner)

Use an admitted pure-Simple Stage 3 or later compiler built from this revision,
with its bootstrap provenance receipt, at bin/release/<host-triple>/simple
(simple.exe on Windows). Record compiler SHA256, revision, phase and backend.
The currently installed seed is not eligible. From the repository root, set
SIMPLE to that absolute executable and run these commands once per matrix cell:

```sh
SIMPLE_LIB=src "$SIMPLE" test test/unit/compiler/hir/class_owner_identity_spec.spl --mode=interpreter
"$SIMPLE" native-build --backend llvm --source test/fixtures/compiler/class_owner_identity/src --entry-closure --entry test/fixtures/compiler/class_owner_identity/src/identity/main.spl --output build/class-owner-identity
build/class-owner-identity
```

On Windows use PowerShell call syntax and an .exe output suffix. Repeat native
compilation with `--backend cranelift`. Required host/backend cells are Windows
x86_64 MSVC and Linux x86_64 GNU, each with LLVM and Cranelift. An unavailable
backend remains explicitly blocked. Expected unit result: all assertions pass;
native exit: 0, including checksum 103034443, nested values 7/17, function-pointer
values 404/73 and array push 73. Inspect definitions and relocations with the
host symbol/object tools: provider Cell methods/default helpers/helper main
must be distinct; entry main, extern, export and @global names retain ABI.

Capture wall elapsed time and process-tree peak RSS using a bounded process
runner (Windows Job Object or Linux cgroup). Stop each unit/native compilation
at 120 seconds or 2 GiB, and each produced executable at 10 seconds or 256 MiB;
exceeding a bound is a recorded failure, not a retry invitation. These are
pending verification budgets, not measured performance claims. Run a warmed
second representative qualified-lookup workload only to obtain the missing
latency/RSS measurement; report preparation and lookup separately. Compare
the same fixture and compiler settings against the parent revision, recording
absolute values and any regression. Provider table reconstruction currently
costs O(provider symbols) per consumer with classes; constructors use indexed
metadata and do not repeat the scan.

Before acceptance also run the required four checks (`check src/compiler`,
`check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`),
`SIMPLE_LIB=src "$SIMPLE" test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`,
and the core/MCP smoke scripts:
`sh scripts/check/check-core-runtime-smoke.shs "$SIMPLE"` and
`SIMPLE_BINARY="$SIMPLE" sh scripts/check/check-mcp-native-smoke.shs`. Record matching admitted MCP/LSP
server paths through MCP_SERVER and LSP_MCP_SERVER. Keep the PR draft until
these runtime, ABI, host/codegen and resource receipts are attached.
