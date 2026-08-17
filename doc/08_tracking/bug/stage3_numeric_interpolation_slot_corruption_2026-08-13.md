# Stage3 numeric interpolation corrupts AST hardening slot (2026-08-13)

Status: Pure-Simple MIR/LLVM root-cause fix implemented; native rebuild and
runtime confirmation remain required because the frozen Build10 executables
crash before focused compile/test execution.

Build9 GDB evidence is retained at `/mnt/data/bs2/packed-memory-build9/gdb-replay/gdb.txt`.
The failing `ast_gen_harden_enabled` load uses `rcx=0x393333373038`, whose little-endian bytes are ASCII `807339`, exactly the preceding `heap_registry=807339` diagnostic value. The array backing pointer for `ast_gen_harden_slot` was therefore overwritten by a numeric-to-text representation. The fault occurs before scalar unboxing; this is not a tuple ABI or AST-hardening predicate defect.

The temporary containment removes dynamic `rt_heap_registry_count()` interpolation from active phase2 and memory-snapshot diagnostics while preserving path, sequence, phase, timing, and live/peak fields. It covers the canonical Build9 environment (`SIMPLE_COMPILER_PHASE_PROFILE`, `SIMPLE_COMPILER_TRACE`, and `SIMPLE_MEM_SNAPSHOT`); those diagnostic owners now contain no heap-count interpolation. Generic numeric interpolation remains enabled elsewhere and is not fixed by the containment change.

The Pure-Simple root fix keeps `rt_raw_i64_to_string` and the other scalar
renderers nominally `i64`: they return tagged runtime-string handles.
`rt_interp_cstr(i64) -> ptr` is the one explicit raw-C-string conversion before
`rt_strcat`; a renderer result is never nominally `Opaque("str")`. LLVM lowering
now registers the same `i64` renderer returns and `ptr` bridge return, so the
generated call sequence preserves the tagged handle before the pointer
conversion. Focused coverage includes numeric extremes, generic interpreter
interpolation, emitted MIR-to-LLVM call shapes, and two
`parser_init_with_path`/`ast_reset` cycles after the diagnostic shape.

Native runtime confirmation is pending a working self-hosted Build10 binary:
the frozen release wrapper fails its bounded `test --help` probe, while the
frozen Stage3 executable segfaults (exit 139) on both the focused SMF compile
and direct native build of the monomorphic numeric diagnostic probe.

---

## 2026-08-17 — the same defect CLASS found and FIXED in the seed's MIR→Cranelift path

The row above concerns the pure-Simple MIR/LLVM lane, where the fix is
"implemented, runtime confirmation pending a working Build10". Independently of
that, the **sibling** lowering in the Rust seed had the same shape of defect and
it was live, reproducible, and is now fixed here. This section is that work; it
does not close the LLVM half of the row.

### RED baseline (before any change)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, the stale Rust bootstrap
seed (`bin/simple --version` prints the seed banner), size 59536728, mtime
2026-08-16 22:59:37. Probe fixture:
`test/fixtures/repro/compiler/scalar_interpolation/scalar_interp_engine_parity_probe.spl`,
run as a subprocess under each engine and diffed.

**12 divergent lines**, all i64, all interpolation:

```
interpreter                              jit
I64_MAX_ANNOT=9223372036854775807        I64_MAX_ANNOT=-1
I64_MAX_INFER=9223372036854775807        I64_MAX_INFER=-1
I64_MAX_TOSTRING=9223372036854775807     I64_MAX_TOSTRING=-1
I64_MAX_FNRET=9223372036854775807        I64_MAX_FNRET=-1
I64_MAX_ARRELEM=9223372036854775807      I64_MAX_ARRELEM=-1
I64_MIN=-9223372036854775808             I64_MIN=0
I64_POW62=4611686018427387904            I64_POW62=0
I64_POW61_MINUS1=2305843009213693951     I64_POW61_MINUS1=-1
I64_POW60=1152921504606846976            I64_POW60=-1152921504606846976
I64_NEG_POW62=-4611686018427387904       I64_NEG_POW62=0
MULTI=9223372036854775807 42 92233...    MULTI=-1 42 -1
NESTED=9223372036854775807 1844674...    NESTED=-1 18446744073709551615
```

`U64_MAX`, `I32_MIN`, `F64`, `BOOL`, `TEXT` and small ints agreed throughout —
the defect was I64-specific, which localised it precisely.

Spec-level RED, same binary:

```
Results: 7 total, 1 passed, 6 failed      # i64_interpolation_engine_parity_spec.spl
Results: 4 total, 2 passed, 2 failed      # scalar_interpolation_engine_parity_sweep_spec.spl
```

### Root cause

`BoxInt` packs a RuntimeValue payload as `(value << 3) | TAG_INT`, so only a
signed **61-bit** magnitude round-trips. The STRESS-F02 fix
(`stress_f02_i64_boxing_truncation_2026-07-17.md`, seed commit 5c71ca50c00)
added an `rt_raw_i64_to_string` bypass for I64 — but **only on the direct
`print(x)` argument path**. Three other lowering sites reach the same runtime
renderers and each kept a U64-only bypass, leaving I64 on the lossy `BoxInt`:

| site | file | reached by |
|---|---|---|
| `MirLowerer::emit_to_string` | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs` | string interpolation `"{x}"` |
| `rt_value_to_string` builtin call | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs` | explicit `rt_value_to_string(x)` |
| `.to_string()`/`.to_text()`/`.str()` method | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs` | `x.to_string()` |

Each now routes I64 through `rt_raw_i64_to_string` exactly as U64 already routed
through `rt_raw_u64_to_string`. Narrow int types (i8..i32, u8..u32) cannot
exceed the 61-bit payload and deliberately stay on `BoxInt`.

### Ablation — causation, not correlation

Four builds from ONE tree into ONE isolated `CARGO_TARGET_DIR`
(`/mnt/data/cargo-i64interp-e29ebf0f`; `bin/simple` and `bin/release/**` were
never touched — ~15 lanes share this checkout):

| build | state | divergent lines |
|---|---|---|
| 0 | deployed stale seed, no fixes | **12** |
| 1 | + `emit_to_string` and `rt_value_to_string` bypasses | 3 |
| 2 | + `.to_string()` method bypass | **1** |
| 3 | **all three guards reverted to U64-only**, rebuilt | **12** (identical line-for-line to build 0) |
| 4 | guards restored, rebuilt | **1** |

Removing the fix regresses the probe to exactly the original 12 lines and
restoring it returns to 1. The fix is reachable and causal.

### AFTER

```
Results: 7 total, 6 passed, 1 failed      # i64_interpolation_engine_parity_spec.spl
Results: 4 total, 2 passed, 2 failed      # scalar_interpolation_engine_parity_sweep_spec.spl
```

Both specs are **deliberately left RED** on the one remaining line. It is not
this defect: `I64_MAX_ARRELEM` is a **distinct root cause** — the value stored
in an `[i64]` array is itself truncated under the JIT, not merely rendered
wrong. Proof it is a data defect and not a rendering defect, on the FIXED
binary:

```
var arr: [i64] = [9223372036854775807]
val e: i64 = arr[0]
print(e == 9223372036854775807)   # interpreter: true   jit: false
print(e + 0)                      # interpreter: 9223372036854775807   jit: -1
```

Filed separately as
`doc/08_tracking/bug/jit_array_element_i64_storage_truncation_2026-08-17.md` per
the one-doc-per-root-cause rule. Per `.claude/rules/testing.md`, a correct spec
that fails is a legitimate artifact: the assertions are right and were not
weakened.

### Cross-lane collision — ACTION REQUIRED by another lane

`test/01_unit/engine_divergence/check-engine-divergence-probes.shs` (worker W5,
landed 2026-08-17) proves its `SIMPLE_EXECUTION_MODE` switch is live by
requiring `probes/boxed_int_61bit_probe.spl` to DIVERGE —
`1152921504606846976` under `interpreter` vs `-1152921504606846976` under
`jit`. That divergence is the `I64_POW60` line fixed here. **Once a seed
carrying this fix is deployed, that positive control stops diverging and W5's
guard will stop passing.** That is correct fail-closed behaviour, not a
regression; W5's lane needs a different liveness control. That file was
deliberately not edited from here.

### Scope

Fixed in the **Rust seed's** MIR lowering, which is what `bin/simple run`
executes today. The pure-Simple MIR/LLVM fix described at the top of this row is
a separate lane and its native runtime confirmation is still pending; this
section does not supply it. Nothing was rebuilt or redeployed into
`bin/` — the verification binary lives in an isolated target dir.

## 2026-08-17 (W6) — collapsed into the interpolation-segment family; not reproduced

This row and
`selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30` were
investigated as ONE family: both are string-interpolation defects, and the
Build9 GDB evidence quoted above is consistent with segment loss rather than
slot corruption. The faulting load held `rcx=0x393333373038` = little-endian
ASCII `807339`, i.e. exactly the `heap_registry` NUMBER with its literal
`heap_registry=` prefix absent — the signature of an interpolated string whose
literal segments were dropped, not of a numeric renderer returning a bad tag.

The segment-preserving behaviour is now pinned by
`test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl`
(`Results: 4 total, 4 passed, 0 failed`), including the exact
`"heap_registry={n} phase={p}"` diagnostic shape with `n = 807339`. Ablating
`access_literal_assign_eval.spl:834` back to a segment-dropping join takes that
spec to `0 passed, 4 failed`, so the guard is real.

The one genuinely drifted copy (`interpreter/eval_access.spl`) has been repaired
— see the 2026-08-17 note on the sibling row. **Status: NOT REPRODUCED on any
source-readable path.** The row's remaining claim ("native rebuild and runtime
confirmation remain required") is still unverified here because no self-hosted
Build10 binary exists in this checkout; that is a missing-evidence gap, not a
live symptom. Leaving OPEN only for that native confirmation.
