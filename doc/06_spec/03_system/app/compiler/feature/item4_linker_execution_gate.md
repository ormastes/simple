# Item4 pending native execution gate

Status: **UNRUN / runtime qualification blocked**. This is an execution recipe
and updated source audit through repair `44d01e5fbcb`, not a claim that
an available executable supports or has passed these commands. No build,
Rust-seed fallback, candidate execution or repeated bootstrap attempt occurred.

## Current production route

The full CLI's `test` dispatch is
`src/app/cli/_CliMain/main_and_help.spl:471` ->
`src/app/test_runner_new/test_runner_main.spl:25` -> the imported
`std.test_runner.test_runner_execute` owner at
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`.
The similarly named app-local executor is not the imported execution owner.

Select the explicit native backend, rather than relying on default interpreter
mode or the plain `--native`/SMF route:

```
<admitted-runtime> test <spec.spl> --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
```

The selected owner preprocesses SSpec into an executable `fn main()`, stages
it through `native_test_stage_source_v1`, builds via `native-build`, prints a
verbose invocation receipt with compiler digest/argv/output, executes the output and parses its
results. Explicit AOT rejects compilation failure instead of accepting a
fallback and rejects zero reported examples. `--keep-artifacts` retains
the generated source/image for inspection; it is not evidence of success.

## Preconditions and currently unresolved admission

Use an admitted pure-Simple full CLI, not the bootstrap-only command subset or
Rust seed. Record its absolute path, SHA256, source revision, qualification and
runtime-bundle lineage. Before execution, set `SIMPLE_BINARY` to that admitted
binary's absolute path; explicit AOT rejects an empty `SIMPLE_BINARY` even if
another runtime selector is available. The required `--verbose` option emits
the invocation receipt, which must identify that binary. A diagnostic `--help` result is not
admission. Windows needs its actual native compiler/runtime dependencies;
Linux likewise needs its qualified LLVM/runtime bundle. WSL is a separate Linux
host context, not evidence that a Windows candidate can execute these tests.

The source repair stages exact transformed bytes in a unique checkout-owned
`test/native-generated-*/entry.spl` directory. Both coverage and explicit AOT
request `--refresh-source-authority` from the compiler child and use canonical
default source roots. Ordinary inherited builds retain their existing contract.
The coordinator consumes the option before workers and acquires/publishes a
fresh immutable generation without modifying the runner parent's environment.
These are source-reviewed changes, not executed admission evidence. Prove the
generated-entry inventory transition and complete compiler/app/lib import
closure with the authored unit, real Git snapshot and backend integration
scenarios; helper generation alone is insufficient. The existing cold-inventory
diagnostics stopped before producing a probe executable:
`doc/08_tracking/bug/item4_source_inventory_cold_init_timeout_2026-10-03.md`.
That record's three-attempt cap remains in force; this manual authorizes no retry.

## Nonvacuous results

Preserve exact spec/source identities, generated source, native invocation
receipt, artifact identity, stdout/stderr, exit status and scenario names.
Every declared scenario below must be accounted for, including its runtime
iterations; skipped/pending/missing cases do not become acceptance passes.
Require nonzero executed examples and zero failing examples, and independently
verify that real assertion paths ran (including a qualified failing-control
result for the harness). Compilation or exit0 alone cannot satisfy this gate.

The current native BDD counters increment at `it` completion
(`src/runtime/simple_core/core_bdd.spl:51`; C owner equivalent
`src/runtime/runtime_native.c:9753`). They are example counts, **not counts of
individual `expect` calls**, despite the runner's zero-assertions diagnostic.
Do not invent an assertion-count receipt from these counters. Source inspection
of real assertions and observed assertion/coverage behavior remain required.

The following are source declaration counts for the manuals corrected in this
change, not execution counts or the complete item4 suite inventory:

| Spec/manual | Declared scenarios |
|---|---:|
| [ELF operations](item4_elf_operations_spec.md) | 11 |
| [ELF source](item4_elf_source_spec.md) | 9 |
| [Mach-O closure](item4_macho_closure_spec.md) | 12 |
| [Mach-O duplicates](item4_macho_duplicates_spec.md) | 6 |
| [Mach-O legacy modes](item4_macho_legacy_modes_spec.md) | 3 |
| [Mach-O legacy reexports](item4_macho_legacy_reexport_spec.md) | 9 |
| [Mach-O provider](item4_macho_provider_spec.md) | 8 |
| [Mach-O runpaths](item4_macho_rpath_spec.md) | 7 |
| [Mach-O TBD](item4_macho_tbd_spec.md) | 9 |
| [macOS native adapter](item4_macos_native_spec.md) | 6 |
| [RISC-V TLS](item4_riscv_tls_ie_spec.md) | 10 |
| [Stream COMDAT](item4_stream_comdat_spec.md) | 13 |
| [Stream COMMON](item4_stream_common_spec.md) | 8 |
| [Stream GOT](item4_stream_got_spec.md) | 6 |
| [Prepared publication](item4_stream_prepare_spec.md) | 4 |

Portable image-byte tests may execute on a qualified Windows or Linux host;
their success would not prove Darwin/FreeBSD/PE/RISC-V native loading. Real
provider-pack suites additionally require their actual built shared artifact,
host prerequisites and expected child exit results. Keep explicit host probes
and full-product/resource gates separate.

## Manuals and repository verification

After qualified execution, generate the mirrored manual with
`<admitted-runtime> spipe-docgen <spec.spl> --output doc/06_spec --no-index` and
require complete scenarios, zero stubs and matching evidence. Source-only
manual generation would still not prove assertions executed.

Required core verification remains `check src/compiler`, `check src/lib`,
`check src/app/mcp`, and `check src/app/simple_lsp_mcp`, plus the existing mandated
`SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`.
That explicitly requested MCP command is unchanged; its own evidence contract
must be assessed separately. Coverage, core/MCP/native smokes, no-stub checks,
host/product execution and NFR receipts remain distinct release gates. Neither
this recipe nor source review establishes Phase4 PASS.
