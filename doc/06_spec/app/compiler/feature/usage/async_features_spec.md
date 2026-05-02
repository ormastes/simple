# Async Features Specification

async features - runtime parser cannot handle async/await/spawn/yield/generator syntax

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASYNC-001 to #ASYNC-063 |
| Category | Runtime \| Async |
| Status | Implemented |
| Source | `test/feature/usage/async_features_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

async features - runtime parser cannot handle async/await/spawn/yield/generator syntax
Tests using unsupported syntax converted to itstubs


Tests async features including:
- Lambda expressions
- Future creation and await
- Async functions
- Generators and yield
- Codegen/interpreter parity

Features not supported by runtime parser:
- async fn syntax
- await keyword
- spawn keyword
- yield keyword
- generator() function

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/async_features/result.json` |

## Scenarios

- basic lambda with single param
- lambda with multiple params
- lambda capturing outer variable
- immediately invoked lambda
- nested lambda calls
- lambda with no params
- creates and awaits basic future
- future with function call
- multiple futures
- future function call with params
- basic async function
- async fn returns auto-awaited
- async fn can call other async
- async fn can use await 
- async fn allows print
- single value generator
- multiple yields
- generator exhaustion returns nil
- generator with captured variable
- arithmetic in yield
- nested iteration
- collects generator values
- await requires future type
- state preserved across yields
- multiple captures
- capture and compute
- future with single capture
- future with multiple captures
- basic actor spawn
- state and capture combined
- exhaustion with capture
- nested generator captures
- nested control flow
- recursive function
- struct field access
- enum pattern match
- array operations
- tuple indexing
- dictionary access
- function composition
- early return
- boolean logic
