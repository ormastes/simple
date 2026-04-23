# Advanced Generics Specification

Tests advanced generic features including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GEN-ADV-001 to #GEN-ADV-008 |
| Category | Type System \| Generics |
| Status | Implemented |
| Source | `test/feature/usage/generics_advanced_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests advanced generic features including:
- Const generic parameters
- Where clauses on functions
- impl Trait for Type syntax
- Nested generic types
- Tuple return types
- Multiple trait bounds
- Associated types

## Syntax

```simple
struct Array<T, const N: usize>:
data: T

fn filled(value: T) -> T where T: Copy:
value

impl Len for MyList:
fn len() -> i64:
self.size

fn make<T>() -> T where T: Clone + Default:
T.default()

trait Iterator:
type Item
fn next() -> Option<Self.Item>
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/generics_advanced/result.json` |

## Scenarios

- parses const generic parameter
- parses where clause on function
- parses impl trait for type
- parses generic impl with where
- parses nested generic types
- parses tuple return type
- parses multiple trait bounds
- parses associated type
