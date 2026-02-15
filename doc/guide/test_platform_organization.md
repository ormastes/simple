# Test Platform Organization Guide

## Three-Tier Test Classification

Every test file falls into one of three tiers based on what platform it can run on:

| Tier | Tag | Directory | Runs On |
|------|-----|-----------|---------|
| **Shared/Core** | `# @platform: all` | `test/shared/` | Host + Baremetal |
| **Host-only** | *(no tag)* | `test/unit/`, `test/integration/` | Host only |
| **Baremetal-only** | `# @platform: baremetal` | `test/baremetal/`, `test/unit/baremetal/` | Baremetal only |

## Directory Layout

```
test/
├── shared/                  # @platform: all — works on host AND baremetal
│   ├── core/                # Core language: arithmetic, types, comparisons
│   ├── control_flow/        # Functions, lambdas, static methods, if/else
│   ├── types/               # Pattern matching, Option, union, contracts
│   └── collections/         # List, map, set operations
│
├── unit/std/                # Host-only stdlib tests (most tests live here)
├── unit/core/               # Host-only compiler core tests
├── unit/app/                # Host-only application tests
├── unit/lib/                # Host-only library tests
│
├── unit/baremetal/          # Baremetal-only unit tests (arch-specific)
├── baremetal/               # Baremetal-only integration tests
│
├── integration/             # Host-only integration tests
├── system/                  # Host-only system tests
└── system/baremetal/        # Baremetal-only system tests (boot, asm)
```

## Platform Tags

Add as the first line of any test file:

```simple
# @platform: all                    # Shared — runs everywhere
# @platform: host                   # Host only (same as no tag)
# @platform: baremetal              # Any baremetal target
# @platform: baremetal(riscv32)     # RISC-V 32-bit only
# @platform: baremetal(arm32)       # ARM Cortex-M only
# @platform: baremetal(aarch64)     # ARM64 only
# @platform: baremetal(x86)         # x86 (i686) only
# @platform: baremetal(x86_64)      # x86_64 (AMD64) only
```

## What Makes a Test "Shared"?

A test is shared (`# @platform: all`) when it:

1. Has **zero imports** (no `use` statements)
2. Uses only **built-in** test functions: `describe`, `it`, `expect`, matchers
3. Uses only **core language features**: arithmetic, strings, arrays, control flow
4. Does **NOT** use: file I/O, process management, threading, networking, timers

### Shared Test Examples

```simple
# @platform: all
describe "Arithmetic":
    it "adds numbers":
        expect(1 + 1).to_equal(2)

    it "factorial":
        var result = 1
        for i in 1..6:
            result = result * i
        expect(result).to_equal(120)
```

### Host-Only Test Examples

```simple
# No tag needed — host is the default
use std.path.{path_join}

describe "Path operations":
    it "joins paths":
        val p = path_join("a", "b")
        expect(p).to_contain("b")
```

### Baremetal-Only Test Examples

```simple
# @platform: baremetal(riscv32)
describe "RV32 Startup":
    it "RAM base address":
        val ram_base = 0x80000000
        expect(ram_base).to_equal(0x80000000)
```

## Filtering Behavior

### Host Mode (default: `bin/simple test`)

- Runs: `test/shared/` + `test/unit/` + `test/integration/` + `test/system/`
- Skips: `test/baremetal/`, `test/unit/baremetal/`, `test/system/baremetal/`
- Skips: Any file with `# @platform: baremetal*` tag

### Composite Mode (`--execution-mode="interpreter(baremetal(riscv32))"`)

- Runs: `test/shared/` + `test/baremetal/` + arch-matching tests
- Skips: Host-only tests (no tag or `# @platform: host`)
- Skips: Wrong-arch tests (e.g., `# @platform: baremetal(arm32)` when targeting riscv32)

## Runtime Skip Helpers

For tests that live in `test/shared/` but have individual tests needing platform-specific behavior:

```simple
# @platform: all

describe "Cross-platform math":
    it "basic addition":
        expect(1 + 1).to_equal(2)

    # Only runs on baremetal targets
    only_on_baremetal "semihost output":
        # test semihost-specific behavior
        expect(true).to_equal(true)

    # Only runs on host
    skip_on_baremetal "file write":
        # test that needs filesystem
        expect(true).to_equal(true)

    # Architecture-specific
    only_on_arch "riscv32", "CSR addresses":
        expect(0x300).to_equal(0x300)
```

Available helpers (from `src/std/spec.spl`):

| Helper | Behavior |
|--------|----------|
| `skip_on_baremetal(name, block)` | Skip when `SIMPLE_RUNTIME_MODE` contains "baremetal" |
| `only_on_baremetal(name, block)` | Run ONLY on baremetal targets |
| `skip_on_remote(name, block)` | Skip when on remote target |
| `only_on_remote(name, block)` | Run ONLY on remote targets |
| `only_on_arch(arch, name, block)` | Run ONLY on specific architecture |
| `skip_on_arch(arch, name, block)` | Skip on specific architecture |

## Current Shared Tests (18 files)

### `test/shared/core/` (6 files)
- `arithmetic_spec.spl` — Addition, subtraction, multiplication, division, precedence
- `comparison_spec.spl` — Equality, ordering, logical operators
- `hello_spec.spl` — Basic print test
- `math_spec.spl` — abs, sign, min/max, clamp, factorial, gcd, lcm
- `minimal_spec.spl` — Minimal passing test
- `primitives_spec.spl` — Integer and boolean operations

### `test/shared/control_flow/` (4 files)
- `fn_lambda_spec.spl` — Functions, lambdas, closures
- `if_else_implicit_return_spec.spl` — If/else, implicit returns
- `no_paren_spec.spl` — No-parentheses call syntax
- `static_fn_spec.spl` — Static method dispatch

### `test/shared/types/` (5 files)
- `contract_spec.spl` — Design by contract (pre/post conditions)
- `option_utils_ext_spec.spl` — Option type utilities
- `pattern_matching_spec.spl` — Match/case expressions
- `try_operator_spec.spl` — Try (?) operator
- `union_impl_spec.spl` — Union type implementations

### `test/shared/collections/` (3 files)
- `list_compact_spec.spl` — List operations
- `map_spec.spl` — Map/dictionary operations
- `set_spec.spl` — Set operations

## Adding New Shared Tests

1. Write the test with zero imports
2. Use only built-in `describe`/`it`/`expect` matchers
3. Add `# @platform: all` as the first line
4. Place in appropriate `test/shared/` subdirectory
5. Run `bin/simple test test/shared/` to verify
