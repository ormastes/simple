# CoreCBootstrap runtime lane cannot link `rt_utf8_*`, `rt_math_sqrt`, `rt_numeric_dot_f64`, `rt_array_remove`

## RESOLVED 2026-09-13 — C twins added, first of the two unblock options taken

All six symbols now have a C definition in `src/runtime/runtime_native.c`,
written beside `rt_array_pop` / the `rt_math_*` libm family because
`RtCoreArray`, `rt_core_as_array` and the tag helpers are file-local to that
translation unit. `runtime_native.c` is the first entry of
`build_c_runtime_library` (`native_project/tools.rs`), so the CoreCBootstrap
archive picks them up with no list edit; `runtime.h` carries the declarations.

The `rt_*` dual-implementation ratchet moved them from single-lane to twinned:
the six `rust-only` rows were REMOVED from
`scripts/check/rt_dual_implementation_baseline.txt` (they are no longer debt to
freeze), and `check-rt-dual-implementation-ratchet.shs` reports
`PASS — 2518 symbol(s) checked against 2518 baselined, 0 new, 0 stale`.

**Eight more libm passthroughs closed in the same change, because six alone did
not move the row.** Re-running the harness on the nine `link` specs proved all
six original symbols resolved, and surfaced the NEXT unresolved set for
`test/01_unit/compiler/backend/llvm_ir_builder_spec.spl`: `rt_math_cbrt`,
`rt_math_cos`, `rt_math_exp`, `rt_math_hypot`, `rt_math_max`, `rt_math_min`,
`rt_math_sin`, `rt_math_tan` — the same Rust-only one-line libm family, trading
one unresolved name for another. They are twinned here too (with `fmin`/`fmax`,
the IEEE minNum/maxNum operations Rust's `f64::min`/`max` are, NOT a `a < b ? a
: b` spelling, which propagates NaN instead) and their eight `rust-only`
baseline rows removed; ratchet `PASS — 2510 checked against 2510 baselined`.

**Parity evidence — one written-down oracle set, asserted independently on both
lanes.** The two runtimes are never linked into one process, so a same-process
A/B is impossible; instead both halves assert values fixed by IEEE-754, RFC 3629
and arithmetic:

- C lane: `src/runtime/test/rt_core_c_utf8_math_array_twin_parity_selfcheck.c`,
  linked against the standalone-compiled `runtime_native.o` (the exact TU the
  archive is built from) — `PASS — 91 check(s), 0 failure(s)` (76 before the
  eight extra math twins were folded in).
- Rust lane: `test/01_unit/runtime/c_lane_utf8_math_array_twin_parity_spec.spl`
  on the seed interpreter — `6 examples, 0 failures`.

Sabotage control (the probe discriminates, it does not merely run): changing the
C `rt_utf8_find_invalid` all-valid return from `-1` to `0` turned the probe red
with `FAIL — 76 check(s), 6 failure(s)`, naming each all-valid case; reverted.
The probe also caught two wrong oracles of the author's own during development
(`count_codepoints` on `C3 28` is 1, not 2), which is the same property.

Deliberate limits, stated rather than papered over:

- `rt_numeric_dot_f64`'s C twin is the sequential `fma` accumulation, which is
  Rust's `scalar_dot_runtime_f64` exactly. Rust additionally routes two
  all-float arrays of length >= 24 (`PACK_THRESHOLD_F64`) through the active
  SIMD provider, whose reassociation can differ in the last ulp. That variance
  already exists *within* the Rust lane across SIMD tiers, so pinning the C lane
  to one host's tier would be worse, not better.
- `rt_numeric_dot_f64` has no interpreter extern registration, so the Simple-side
  spec cannot exercise it; its oracles are in the C probe and the Rust crate's
  own `numeric_kernels.rs` tests.
- No pure-Simple twin / `# @dual_pair:` annotation was added:
  `check-dual-run-shadow.shs` requires a runnable `bin/simple test`, which this
  host does not have, and an annotation that cannot be run is an unverifiable
  pair. That remains open follow-up work.

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
