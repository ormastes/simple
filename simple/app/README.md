# Simple Formatter & Linter

Implementation of canonical formatting and semantic linting for Simple language, written in Simple itself.

## Structure

```
simple/
├── app/
│   ├── formatter/
│   │   └── main.spl          # Formatter implementation
│   └── lint/
│       └── main.spl          # Linter implementation
├── bin_simple/               # Compiled executables
│   ├── simple_fmt           # Formatter binary
│   └── simple_lint          # Linter binary
├── build/                    # Intermediate build files
│   ├── formatter/           # Formatter .smf files
│   └── lint/                # Linter .smf files
└── build_tools.sh           # Build script
```

## Features

### Formatter (`simple_fmt`)

Canonical, zero-configuration formatter based on `doc/spec/formatting_lints.md`.

**Features:**
- ✅ Deterministic formatting (no configuration)
- ✅ 4-space indentation (always)
- ✅ Idempotent (format(format(x)) == format(x))
- ✅ Check mode (`--check`) for CI
- ✅ In-place formatting (`--write`)
- ⚠️ Basic line-by-line formatter (TODO: AST-based)

**Usage:**
```bash
# Print formatted output
./simple/bin_simple/simple_fmt file.spl

# Check if file is formatted (CI mode)
./simple/bin_simple/simple_fmt file.spl --check

# Format file in place
./simple/bin_simple/simple_fmt file.spl --write
```

### Linter (`simple_lint`)

Semantic linter with multiple lint categories based on `doc/spec/formatting_lints.md`.

**Lint Categories:**
- **Safety (S)**: Memory safety, null checks
- **Correctness (C)**: Logic errors, type mismatches
- **Warning (W)**: Potential issues, unused code
- **Style (ST)**: Naming conventions (allow by default)
- **Concurrency (CC)**: Thread safety issues

**Features:**
- ✅ Multiple lint levels (Allow/Warn/Deny)
- ✅ Fix-it hints in output
- ✅ Category-based organization
- ✅ Deny-all mode for strict checking
- ⚠️ Pattern-based linting (TODO: AST-based semantic analysis)

**Usage:**
```bash
# Run linter
./simple/bin_simple/simple_lint file.spl

# Treat warnings as errors
./simple/bin_simple/simple_lint file.spl --deny-all

# Enable all lints including style
./simple/bin_simple/simple_lint file.spl --warn-all
```

**Example Output:**
```
file.spl:10:0: warning[W001]: Unused variable (prefix with _ to silence)
  hint: Remove declaration or assign a value

file.spl:25:0: error[S001]: Unused Result type (must use .unwrap(), .expect(), or match)

Found 1 error(s) and 1 warning(s)
```

## Building

### Prerequisites

1. Simple compiler must be built:
   ```bash
   cargo build
   ```

2. Compiler should be available at `./simple/bin/simple`

### Build Tools

Run the build script:
```bash
./simple/build_tools.sh
```

This will:
1. Compile `formatter/main.spl` → `bin_simple/simple_fmt`
2. Compile `lint/main.spl` → `bin_simple/simple_lint`
3. Place intermediate files in `build/`

### Manual Build

If you need to build manually:
```bash
# Build formatter
./simple/bin/simple compile simple/app/formatter/main.spl \
    --output simple/bin_simple/simple_fmt \
    --build-dir simple/build/formatter

# Build linter
./simple/bin/simple compile simple/app/lint/main.spl \
    --output simple/bin_simple/simple_lint \
    --build-dir simple/build/lint
```

## Implementation Status

### Formatter

| Feature | Status | Notes |
|---------|--------|-------|
| Basic indentation | ✅ | 4-space indent |
| Line-by-line formatting | ✅ | Simple implementation |
| Check mode | ✅ | Exit 1 if not formatted |
| Write mode | ✅ | Format in place |
| AST-based formatting | ⚠️ TODO | Requires parser integration |
| Comment preservation | ⚠️ TODO | Requires parser |
| Max line length | ⚠️ TODO | Requires smart wrapping |

### Linter

| Feature | Status | Notes |
|---------|--------|-------|
| Safety lints | ✅ | Basic pattern matching |
| Correctness lints | ✅ | Basic pattern matching |
| Warning lints | ✅ | Unused variables |
| Style lints | ✅ | Naming conventions |
| Concurrency lints | ⚠️ Partial | Needs semantic analysis |
| Fix-it hints | ✅ | Text suggestions |
| AST-based analysis | ⚠️ TODO | Requires compiler integration |
| Control flow analysis | ⚠️ TODO | Requires compiler integration |

## Roadmap

### Phase 1: Basic Implementation (Current)
- ✅ Line-by-line formatter
- ✅ Pattern-based linter
- ✅ Command-line interface
- ✅ Build infrastructure

### Phase 2: AST Integration
- ⏳ Parse .spl files to AST
- ⏳ AST-based formatting
- ⏳ Semantic analysis for lints
- ⏳ Control flow analysis

### Phase 3: Advanced Features
- ⏳ Auto-fix (`simple fix`)
- ⏳ IDE integration (LSP)
- ⏳ Configuration in simple.sdn
- ⏳ Lint explanation (`--explain`)

## Testing

Create a test file:

```simple
# test.spl
fn  example( ):
let x=1
if x>0:
print("hello")
```

Format it:
```bash
./simple/bin_simple/simple_fmt test.spl --write
```

Result:
```simple
# test.spl
fn example():
    let x = 1
    if x > 0:
        print("hello")
```

Lint it:
```bash
./simple/bin_simple/simple_lint test.spl
```

## Contributing

When implementing new lints or formatting rules:

1. Update `doc/spec/formatting_lints.md` with specification
2. Add feature to `doc/features/feature.md`
3. Implement in `simple/app/formatter/` or `simple/app/lint/`
4. Add tests
5. Update this README

## References

- **Spec**: `doc/spec/formatting_lints.md`
- **Features**: `doc/features/feature.md` (#1131-#1145)
- **Examples**: `simple/test/` directory
