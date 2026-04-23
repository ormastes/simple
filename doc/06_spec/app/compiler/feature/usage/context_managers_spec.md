# Context Managers Specification

Context managers provide a way to safely acquire and release resources using

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTEXT-MANAGER |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/context_managers_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Context managers provide a way to safely acquire and release resources using
the `with` statement. They implement the resource protocol with `__enter__()` and
`__exit__()` methods, ensuring cleanup code runs reliably even when exceptions occur.

## Syntax

```simple
with resource as alias:
```

## Key Behaviors

- `__enter__()` is called on entry, its return value is bound to alias
- `__exit__()` is always called, even if an exception occurs
- Alias binding can coexist with parser special handling (e.g., cast expressions)
- Clean separation between resource acquisition and usage
- Exception safety: cleanup always happens

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/context_managers/result.json` |

## Scenarios

- calls __enter__ and binds result to alias
- calls __exit__ after block completes
- reuses identifier when parser sees cast-style syntax
- properly binds alias in nested contexts
- runs cleanup code after block
- runs cleanup even after multiple operations
- can use alias from __enter__ return value
- can call methods on alias
- passes exception info to __exit__
- always calls __exit__ for resource cleanup
- can nest multiple context managers
- cleans up in reverse order
- implements file-like resource pattern
- ensures state is restored on exit
