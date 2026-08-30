# Test-runner environment ABI integration specification

> Exercises the production environment facade used by the test runner.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

Source: `test/02_integration/app/test_runner_env_abi_spec.spl`

## Scenario

### Should round-trip a configured environment value

Preserve the prior value, write a non-pointer-shaped text value through the
environment facade, read the exact value back, and restore the prior value.

The executable scenario must run on the admitted pure-Simple runner; the Rust
seed is not substitute evidence.
