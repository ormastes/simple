# Core + MCP source-matched runtime qualification gap

Status: OPEN — runtime qualification missing; no failing CI step observed.

Observed: 2026-09-28 04:36 UTC. This report is based on immutable Git objects and GitHub run metadata, not dirty source files in the main worktree. The isolated report branch starts at local `origin/main` commit `fdc600a4d3f56b068715ffe650e0841db17700ea`; that local reference is not a claim about the latest remote main commit.

## Concrete gap

Core + MCP Dev Pipeline currently exercises the Rust bootstrap executable. A successful result therefore does not establish that the pure-Simple self-hosted compiler at the same source revision can execute the required compiler, library, and MCP/LSP checks. Repository policy reserves the Rust seed for bootstrap and requires self-hosted runtime qualification for normal tooling.

Immutable workflow evidence, from PR #1960 head `2cc416871b761d3f3c3f3edd8bfcc934e1b888ea`:

- [Lines 107–111](https://github.com/ormastes/simple/blob/2cc416871b761d3f3c3f3edd8bfcc934e1b888ea/.github/workflows/core-mcp-dev-pipeline.yml#L107): build `simple-driver` and `simple-native-all` with Cargo bootstrap profile.
- [Lines 113–116](https://github.com/ormastes/simple/blob/2cc416871b761d3f3c3f3edd8bfcc934e1b888ea/.github/workflows/core-mcp-dev-pipeline.yml#L113): verify and invoke `src/compiler_rust/target/bootstrap/simple`.
- [Lines 118–123](https://github.com/ormastes/simple/blob/2cc416871b761d3f3c3f3edd8bfcc934e1b888ea/.github/workflows/core-mcp-dev-pipeline.yml#L118): set `SIMPLE_BINARY` to that Rust executable and check `src/compiler` and `src/lib`.
- [Lines 125–133](https://github.com/ormastes/simple/blob/2cc416871b761d3f3c3f3edd8bfcc934e1b888ea/.github/workflows/core-mcp-dev-pipeline.yml#L125): use the same executable for MCP/LSP checks and interpreter tests.

No pure-Simple compiler build or replacement of the selected runtime intervenes between these steps. The inspected local `origin/main` workflow has the same wiring.

## Current CI observations

| PR | Observed head | Core + MCP run | Phase |
|---|---|---|---|
| #1960 | `2cc416871b761d3f3c3f3edd8bfcc934e1b888ea` | [36375221544](https://github.com/ormastes/simple/actions/runs/36375221544) | In progress: Core runtime smoke |
| #1962 | `c1deebb2198b4e435039646f61845408ab99b654` | [36375372421](https://github.com/ormastes/simple/actions/runs/36375372421) | In progress: Core runtime smoke |
| #1973 | `dd4ccd7b53f595e585e13723c5e0f13b60dd6e91` | [36376900806](https://github.com/ormastes/simple/actions/runs/36376900806) | In progress: Core runtime smoke |
| #1974 | `83fdee17b83fcd44a712276a1f0d1cd19c168ed4` | [36376910614](https://github.com/ormastes/simple/actions/runs/36376910614) | In progress: Core runtime smoke |
| #1983 | `867423d67c15eaa6566d91902f50d84208979b4b` | No branch run found | Unverified |

No failed step was reported in the four running jobs. Native MCP/LSP smoke has not yet supplied admission evidence. A running phase is not a failure or a PASS. No workflow was dispatched or cancelled, and no check was rerun for this report.

## Local artifact limitations

Release executables exist locally, but this audit did not establish a source-matched pure-Simple runtime for any listed PR head. The release receipt found at `bin/release/aarch64-apple-darwin-macho/simple.arm64-compiler-receipt.env` records `compiler_version=simple-bootstrap 1.0.0-beta`, a binary hash, and a native smoke result, but no source commit. Its August timestamp predates the September 18 executable timestamp. This is insufficient provenance; it does not prove that no usable compiler exists elsewhere.

A bounded search of tracked documentation and open GitHub issues did not identify a dedicated issue for this exact workflow runtime substitution. This report is the concrete tracking item; it is not a production verification PASS.

## Required correction and acceptance evidence

1. Bootstrap a pure-Simple self-hosted compiler from the exact checked-out candidate. The Rust seed may build the compiler; required runtime admission checks must execute the resulting self-hosted artifact.
2. Emit a receipt containing the source commit (and tree identity or recorded source changes), target triple, compiler artifact SHA-256, compiler implementation/stage, bootstrap input identity, build command/configuration, and result. Cache reuse must verify the recorded source and configuration match the candidate; missing or mismatched provenance must stop qualification.
3. Record the resolved compiler path and SHA-256 in each required gate result and match them against the receipt. Prevent silent fallback to the Rust seed or an older deployed compiler.
4. With that artifact, pass `check src/compiler`, `check src/lib`, `check src/app/mcp`, and `check src/app/simple_lsp_mcp`; pass the existing MCP wrapper contract and lazy-project-source regression; run `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`. Preserve required assertions and report the first real failing gate if the current source fails.
5. Complete the required core runtime smoke and MCP native smoke using the same candidate and retain their receipts. For package/publish changes, also native-build both server entry closures and run the isolated npm package smoke. Record which conditional gates apply.
6. Add meaningful provenance validation covering a mismatched source revision and a mismatched binary hash; both must fail admission. A positive case must prove the invoked executable matches the accepted receipt.
7. Publish immutable run/artifact links for the candidate revision. Keep running or missing jobs marked pending. Close this item only after the self-hosted qualification completes successfully; existing Rust-seed results cannot satisfy it.

This report proposes acceptance criteria only. No workflow or compiler implementation was modified, and no new runtime qualification was attempted.
