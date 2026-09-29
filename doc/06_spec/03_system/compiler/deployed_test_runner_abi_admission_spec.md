# Deployed test-runner ABI admission system specification

> Proves that the production wrapper reaches a healthy deployed pure-Simple
> test runner. A signal exit is failure; the Rust seed is not an alternate.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

Source: `test/03_system/compiler/deployed_test_runner_abi_admission_spec.spl`

## Scenario

### Should complete the production test help path

Run `bin/release/simple test --help` with a bounded timeout, require exit zero,
and require the combined output to identify the test surface.

This scenario becomes admission evidence only when executed by the deployed
pure-Simple runner produced by the canonical pipeline.
