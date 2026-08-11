# LLM Caret Cached CLI Qualification

> Exercises the shipped cached Caret CLI through a fail-closed qualification
> checker and retains scrubbed command/output evidence for every case.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 3 | 3 | 0 | 0 |

This manual records zero executed scenarios and does not claim PASS because a
qualified cached Caret artifact is not currently available.

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / CLI |
| Status | Active; execution requires a qualified cached Caret artifact |
| Requirements | REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006 |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl` |
| Checker | `scripts/check/check-llm-caret-cli-cached.shs` |
| Generator | Manual synchronization; docgen execution remains a qualification gate |

## Scope

The checker accepts only `bin/caret` backed by a cached native artifact with a
matching provenance manifest. It validates the committed source identity,
binary and runtime SHA-256 values, target, pure-Simple self-hosted runtime
identity, successful runtime probe, and explicit absence of a Rust seed. It
then disables source fallback and runs fixed offline Claude-fixture requests.

Each case retains `command.txt`, scrubbed `stdout.txt`, scrubbed `stderr.txt`,
`exit.txt`, `provenance.txt`, and `combined.txt` under
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_cli_cached/<case>/`.
CLI evidence is text/process capture; it has no terminal screen or raster
screenshot claim. Fixture secrets are scrubbed before retained output is saved.

## Scenarios

### should verify the cached artifact and its provenance before qualification

1. Load the cached Caret artifact.
2. Invoke the offline Caret CLI provider.
3. Check captured output and status.

The prerequisite case reports the resolved artifact and provenance paths,
matching source identity, verified binary/runtime hashes, self-hosted runtime
identity, and a zero exit only when all qualification checks pass.

### should return the offline Claude response from the cached executable

1. Load the cached Caret artifact.
2. Invoke the offline Caret CLI provider.
3. Check captured output and status.

The fixed Claude fixture must return `fixture-ok` through the cached executable;
the case saves its complete scrubbed process evidence.

### should preserve cached provider failure and usage evidence

1. Load the cached Caret artifact.
2. Invoke the offline Caret CLI provider.
3. Check captured output and status.

The checker runs a deterministic provider failure and unknown-option rejection.
It requires their expected nonzero exits while the enclosing evidence checker
returns zero, and it rejects a retained fixture secret.

## Execution Boundary

Missing artifact, provenance, runtime identity, hash, fixture, or required
capture evidence is a failure, never a skip. These scenarios become executed
evidence only after a provenance-qualified cached Caret artifact is supplied;
until then this manual intentionally reports zero execution.

</details>
