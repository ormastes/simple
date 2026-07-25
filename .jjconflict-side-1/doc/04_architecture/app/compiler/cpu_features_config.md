# CPU Feature Configuration (`SIMPLE_CPU_FEATURES`)

The Simple compiler (Cranelift JIT + AOT) reads the `SIMPLE_CPU_FEATURES`
environment variable to enable or disable individual ISA extensions.

## Format

```
SIMPLE_CPU_FEATURES=<token>[,<token>...]
```

Each token is `+name` (enable), `-name` (disable), or bare `name` (enable).
Tokens are comma-separated; whitespace around commas is trimmed.

## Examples

```bash
# Disable AVX2 (scalar fallback on x86_64)
SIMPLE_CPU_FEATURES=-avx2 bin/simple build

# Disable AVX-512 while keeping the rest of x86-64-v4
SIMPLE_CPU_FEATURES=-avx512f,-avx512vl bin/simple build

# Combine with CPU level: v3 preset minus AVX2
SIMPLE_CPU_FEATURES=-avx2 bin/simple build --cpu x86-64-v3

# Force scalar ARM (accepted but currently no-op — see caveat below)
SIMPLE_CPU_FEATURES=-neon bin/simple build
```

## Recognized tokens

| Token     | ISA     | Cranelift flag  | Notes                              |
|-----------|---------|-----------------|-------------------------------------|
| `sse3`    | x86_64  | `has_sse3`      |                                     |
| `ssse3`   | x86_64  | `has_ssse3`     |                                     |
| `sse41`   | x86_64  | `has_sse41`     |                                     |
| `sse42`   | x86_64  | `has_sse42`     |                                     |
| `avx`     | x86_64  | `has_avx`       |                                     |
| `avx2`    | x86_64  | `has_avx2`      |                                     |
| `avx512f` | x86_64  | `has_avx512f`   |                                     |
| `avx512vl`| x86_64  | `has_avx512vl`  |                                     |
| `bmi1`    | x86_64  | `has_bmi1`      |                                     |
| `bmi2`    | x86_64  | `has_bmi2`      |                                     |
| `fma`     | x86_64  | `has_fma`       |                                     |
| `lzcnt`   | x86_64  | `has_lzcnt`     |                                     |
| `popcnt`  | x86_64  | `has_popcnt`    |                                     |
| `neon`    | aarch64 | —               | **No-op** — no Cranelift flag       |
| `sve`     | aarch64 | —               | **No-op** — no Cranelift flag       |
| `sve2`    | aarch64 | —               | **No-op** — no Cranelift flag       |
| `sse2`    | x86_64  | —               | **No-op** — unconditional baseline  |

Unknown tokens are logged to stderr (`simple: unknown cpu feature token 'X' ignored`)
and have no effect.

## Interaction with `--cpu` levels

Feature overrides are applied **after** the CPU-level preset. This means:

```bash
# Get x86-64-v3 (avx2 + bmi1 + fma + ...) but without AVX-512 variants
SIMPLE_CPU_FEATURES=-avx512f,-avx512vl bin/simple build --cpu x86-64-v4
```

## Caveat

Disabling a feature that generated code actually uses will produce Cranelift
verification errors or incorrect code at JIT / AOT time. Use with care when
testing scalar fallback paths — do not use in production unless you have
verified the generated code does not rely on the disabled extension.

## Rust API

```rust
// Programmatic override (bypasses env var)
let settings = BackendSettings::aot()
    .with_cpu_features(CpuFeatureConfig::from_env_string("-avx512f"));
```
