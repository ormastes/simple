---
name: Coding Language Reference
description: Simple language syntax rules, common mistakes from other languages, type names, lambda shorthands, EasyFix rules
type: reference
---

## Common Mistakes
| From | Wrong | Correct |
|------|-------|---------|
| Python | `def`, `None`, `True` | `fn`, `nil`, `true` |
| Rust | `let mut`, `fn(&mut self)`, `::<T>` | `var`, `me fn()`, `<T>` |
| Java/C++ | `new Point()`, `this.x`, `public` | `Point{}`, `self.x` (implicit), `pub` |
| TS | `function`, `const`, `interface` | `fn`, `val`, `trait` |

## Variables
- `val x = 1` (immutable, preferred), `var x = 1` (mutable)
- Strings: `"interpolated {x}"`, `'raw no {interp}'`. NO `f""` prefix.

## Type Names
- NO `Int`/`Float` — use `i32`, `i64`, `f32`, `f64`, `u8`, etc.

## Methods (implicit self)
- `static fn new()` — no self. `fn get()` — immutable. `me set()` — mutable.
- `self.field` in body. Functions are public by default; `_prefix` for private.

## Lambda Shorthands
- `_ * 2` → `\p: p * 2`. `_1 + _2` → numbered. `&:len` → method ref.
- `curry2(\a,b: a+b)`, `partial1(\a,b: a*b, 3)`

## Contracts
```simple
fn divide(a: i32, b: i32) -> i32:
    in: b != 0, "non-zero"
    out(ret): ret * b == a or a % b != 0
    a / b
```

## Effects: `@pure`, `@io`, `@fs`, `@net`, `@unsafe`

## EasyFix Rules (9)
print_in_test_spec, unnamed_duplicate_typed_args, resource_leak, sspec_missing_docstrings, sspec_manual_assertions, non_exhaustive_match, typo_suggestion, parser_contextual_keyword, type_mismatch_coercion

## Commands
```bash
bin/simple build lint           # Check warnings
bin/simple fix file.spl --dry-run  # Preview fixes
bin/simple lint file.spl --fix     # Auto-fix
```

## MDSOC+ for OS Userland

When writing code under `src/os/services/` or `src/os/apps/`: use **MDSOC+** — MDSOC capsule outer + ECS business layer inner. Model processes, sockets, windows, files, tabs, etc. as ECS entities with components, not as nested structs. Stdlib: `use std.ecs`. Kernel/drivers stay MDSOC-only. See `ref_architecture.md` §MDSOC+ and `doc/04_architecture/mdsoc_architecture_tobe.md` §Part 3.
