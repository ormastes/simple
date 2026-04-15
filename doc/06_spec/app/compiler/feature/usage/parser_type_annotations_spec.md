# Parser Type Annotations Specification

Tests that the parser correctly parses type annotations including

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-TYPE-001 to #PARSER-TYPE-012 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_type_annotations_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly parses type annotations including
SIMD types, unit types, typed strings, and array types.

## Type Syntax

```simple
let v: vec[4, f32] = simd_vec

unit UserId: i64 as uid
unit IpAddr: text | u32 as ip

let addr = "127.0.0.1"_ip
let path = 'C:/data.txt'_file

let arr: [i32] = []       # Dynamic
let fixed: [i32; 10] = [] # Fixed size
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_type_annotations/result.json` |

## Scenarios

- parses vec[4, f32] type
- parses vec[8, i32] type
- parses vec[2, f64] type
- parses SIMD function parameters
- parses SIMD return type
- parses unit with single base type
- parses unit with suffix
- parses unit with two base types
- parses unit with multiple base types
- parses string with _ip suffix
- parses raw string with _file suffix
- parses string with _http suffix
- parses string with custom suffix
- parses [i32] type
- parses [text] type
- parses nested array type
- parses [i32; 10] type
- parses [f64; 3] type
- parses Option<T> type
- parses Result<T, E> type
- parses nested generic type
- parses generic with multiple params
- parses fn type annotation
- parses fn with multiple params
- parses fn returning unit
- parses (i64, text) type
- parses triple tuple
- parses nested tuple
- parses mutable reference
- parses immutable reference
- parses Option<[i64]>
- parses Result<(i64, str), str>
- parses fn returning Option
