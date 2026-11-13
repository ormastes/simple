# A declared-type mismatch compiles and runs with no error (native-build and `run`)

- **Date:** 2026-11-13
- **Status:** OPEN — needs type-system owner
- **Severity:** high (a lost error: exit 0, artifact emitted, nothing on stderr)
- **Found by:** Phase 3 compile-error reporting catalog, case 6
  (`p3_compile_error_reporting_catalog_2026-11-13.md`)
- **Related:** `check_silently_passes_type_errors_parse_only_2026-09-01.md`
  (same inputs through `simple check`, which is parse-only)

## Reproduction

```spl
# p2_type.spl
fn main() -> i64:
    val x: i64 = "s"
    0
```

```spl
# p7_type_text.spl
fn main() -> i64:
    val t: text = 5
    print t
    0
```

| producer | command | result |
|---|---|---|
| run-21 `stage2-admitted/simple` (pinned `554460a6b85a`) | in-process positional `native-build <f> --backend cranelift --runtime-bundle core-c-bootstrap --threads 1 --emit-object -o <o>` | `rc=0` for both, object written, no diagnostic |
| Rust seed `src/compiler_rust/target/bootstrap/simple` | `run <f>` | `rc=0` for both; p7 prints `<value:0x5>` |

So it is language-wide, not a native-build reporting defect: neither the HIR
lowering nor the MIR lowering on the native-build path rejects an initializer
whose type contradicts the declared binding type, and the seed interpreter does
not either. The `[bootstrap-error-count]` probes in the native-build log stay
at `count=0` through `post-lowering`, `post-diagnostics` and `post-store`.

Contrast (same producer, same route): unresolved name (HIR), unresolved method
(MIR), unresolved import and parse errors are all reported with file:line:col.

## Expected

`E1003` (`TYPE_MISMATCH`, `src/compiler/00.common/error_codes.spl`) at the
initializer's span, failing the module.

## Not done here

The error-reporting lane does not own type checking; no fix attempted.
