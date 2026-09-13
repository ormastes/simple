# CoreCBootstrap runtime lane cannot link `rt_utf8_*`, `rt_math_sqrt`, `rt_numeric_dot_f64`, `rt_array_remove`

- Filed: 2026-09-13
- Found by: `scripts/check/check-native-interp-differential.shs` (first census)
- Census: `doc/10_metrics/infra/native_interp_differential_2026-09-13.md`
- Seed: `build/cargo-f52/release/simple`, sha256 `7b388bd1f570cb14…`
- Lane: `SIMPLE_NATIVE_BUILD_RUST=1 … native-build --mode dynload --backend cranelift`
- Class: `link` (a native-build failure is a divergence, not a skip)

## Symptom

Six of 31 compared pure-logic specs fail to native-build at all, each with the
fail-closed unresolved-symbol preflight
(`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`):

```
Build failed: N runtime symbol(s) referenced by generated code have no definition
in any linked object, runtime archive, or system library: …
```

Aggregated over the census's build logs, the unresolved names outside the known
process/mmap set are:

| symbol | specs |
|---|---|
| `rt_utf8_validate` | 5 |
| `rt_utf8_find_invalid` | 5 |
| `rt_utf8_count_codepoints` | 5 |
| `rt_math_sqrt` | 1 |
| `rt_numeric_dot_f64` | 1 |
| `rt_array_remove` | 1 |

Affected specs: `encoding/utf32_byte_guard_spec.spl`,
`encoding/protobuf_wire_bounds_guard_spec.spl`,
`encoding/codec_decode_byte_guard_spec.spl`, `search/explain_contract_spec.spl`,
`engine/math3d_trig_precision_repro_spec.spl`,
`web/browser_renderer_frame_reuse_protocol_spec.spl`.

## Why this is a real gap, not harness noise

The default native runtime lane with no bundle flag is **CoreCBootstrap**
(`pipeline/native_project/config.rs`), which builds a C-only archive from
`src/runtime/*.c`. These six symbols are implemented in the **Rust** runtime
crate only, so the C-only lane can never define them — which is exactly the
`rt_*` dual-implementation gap `check-rt-dual-implementation-ratchet.shs` freezes
(2,488 single-lane symbols as of 2026-09-01). This record names six of them that
have an observed, reproducible consequence: ordinary pure-logic Simple code that
validates UTF-8, takes a square root, dots two `f64` vectors, or removes an array
element **cannot be natively built on the bootstrap runtime lane**.

Distinct from the five process/mmap externs
(`rt_exec`, `rt_execute_native`, `rt_get_host_target_code`, `rt_mmap`,
`rt_process_run_with_limits`) that the spec harness declares transitively but
never calls for a pure-logic spec. The harness treats only those five as inert
and bypasses them under `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` with the retry
recorded per row; **the six above are never bypassed** — they are live call
targets, so a NULL GOT slot would be a SEGV on first use, and the build is
correctly left failing.

## Reproducer

```sh
SIMPLE_NATIVE_BUILD_RUST=1 build/cargo-f52/release/simple native-build \
  --source src/lib --source test --entry-closure --mode dynload \
  --backend cranelift --threads 1 \
  --entry test/01_unit/lib/common/encoding/utf32_byte_guard_spec.spl -o /tmp/a.out
```

## Unblock condition

Either a pure-Simple / C twin for each symbol under `src/runtime/` (the repo's
stated pure-Simple-first, C-boundary policy — `doc/07_guide/os/hal/pure_simple_hal.md`),
or an explicit decision that these six belong to a Rust-only lane and that the
CoreCBootstrap lane's coverage limit is documented where a native-build user
meets it. **Not fixed here** — this lane's product is the harness and the census;
F65 owns the seed.
