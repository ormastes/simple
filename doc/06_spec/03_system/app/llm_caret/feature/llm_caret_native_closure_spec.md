# LLM Caret Native Closure Release Gate

> Builds the production Caret entry closure with a supplied simple-core archive
> and rejects bootstrap/seed runtimes, stub fallback, missing artifacts, and
> unresolved Caret ABI symbols.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 2 | 2 | 0 | 0 |

This manual records zero executed scenarios. A qualified self-hosted runtime
and explicit simple-core archive have not yet been supplied for this gate.

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / native build release gate |
| Requirements | REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl` |
| Checker | `scripts/check/check-llm-caret-native-closure.shs --check` |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Evidence | `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_native_closure/` |

## Mandatory Release Gate

Run the direct checker before the SSpec release lane. It accepts only the
canonical self-hosted runtime at `bin/release/<host-target>/simple`, unless
`SIMPLE_CARET_RUNTIME_PATH` explicitly supplies another executable whose version
output contains neither `Bootstrap` nor `seed`. It requires one supplied archive
path through `SIMPLE_SIMPLE_CORE_PATH` or `SIMPLE_CORE_RUNTIME_PATH`; conflicting
paths fail closed.

The checker invokes `native-build` with `--entry-closure`,
`--entry src/app/llm_caret/main.spl`, `--runtime-bundle simple-core`, and
`SIMPLE_NO_STUB_FALLBACK=1`. It requires an executable output and scans `nm -u`
for the Caret process, directory, terminal, input, and thread ABI symbols that
previously made the closure link fail. Every failure reports exactly
`closure_status=FAIL`, `failure_class=release_gate`, and a stable
`failure_reason=<reason>` before returning nonzero.

The checker retains `build.args.txt`, `build.stdout.txt`, `build.stderr.txt`,
`build.exit.txt`, `runtime.version.txt`, `provenance.txt`, `undefined-symbols.txt`,
`caret-abi-undefined.txt`, and status files. These are process/binary artifacts,
not provider or raster-screen evidence.

## Scenarios

### should build the Caret entry closure from the qualified self-hosted runtime

1. Prepare the self-hosted native closure.
2. Build the Caret entry closure.
3. Check artifact provenance and status.

The direct checker must finish with `closure_status=PASS` and exit zero.

### should retain deterministic build and ABI evidence for the qualified artifact

1. Prepare the self-hosted native closure.
2. Build the Caret entry closure.
3. Check artifact provenance and status.

The direct checker must retain the build invocation, exit, stdout/stderr,
self-hosted runtime and archive hashes, source revision, output hash, and the
empty Caret-ABI unresolved-symbol report.

## Execution Boundary

The SSpec is an executable mirror of the direct release gate; it is not a
substitute for running the checker before release. Missing runtime/archive,
build failure, failed `nm`, or a Caret ABI unresolved symbol is a release-gate
FAIL, never a skip or a bootstrap fallback. Until the qualified inputs exist,
this manual intentionally claims no execution PASS.

</details>
