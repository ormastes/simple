# Native/JIT: `f(...).to_i32()` on an f64-returning call converts the raw bit pattern

- **Filed:** 2026-11-23
- **Class:** silent wrong value, seed codegen (native-build with
  `SIMPLE_NATIVE_BUILD_RUST=1`, and `simple run` on the Rust seed)
- **Status:** fixed in the Rust seed (Cranelift JIT + native-build), branch
  `work/compiler-native-f64-call-conv-20261123`. The Engine2D workarounds stay
  until the seed that builds the GB10 worker is rebuilt from a tree with the
  fix (see "Remaining workarounds").

## Repro

```simple
use std.common.numeric_round.{ceil_f64, floor_f64}

fn local_floor(x: f64) -> f64:
    val t = x as i64 as f64
    if t > x: t - 1.0 else: t

fn main() -> i64:
    val x = 47.26617698462807
    print "A {floor_f64(x).to_i32()} {ceil_f64(240.3).to_i32()}"   # 0 0      (want 47 241)
    val f: f64 = floor_f64(x)
    print "B {f.to_i32()}"                                        # 47
    print "C {floor_f64(x) as i32}"                               # 47
    print "D {local_floor(x).to_i32()}"                           # 0        (want 47)
    print "E {floor_f64(x).to_i64()}"                             # 4631811479262199808 (want 47)
    val g = floor_f64(x)
    print "F {g.to_i32()}"                                        # 47
    0
```

The output is the same from a native-build binary (seed
`~/.cache/cargo-target-wr-gpulink/release/simple`, `--runtime-bundle
host-gpu-native-all`, aarch64 GB10) and from `simple run` on the
webrender-blend seed. `.to_i64()` returns the IEEE-754 bits of 47.0
(`0x4047800000000000`), and `.to_i32()` returns their low 32 bits, which are 0.
A local function shows it too (D), so the defect is not about imports. The
interpreter used by `simple test` returns 47, so an interpreted spec cannot
catch it.

## Trigger

A method-call conversion (`.to_i32()` / `.to_i64()`) whose receiver is a
**call expression** returning `f64`. A receiver bound to a local (typed or
untyped) converts correctly, and so does `as i32`.

## Impact found

`_engine2d_draw_ir_strict_vulkan_affine_pixels` (`draw_ir_adv.spl`) computed
the affine dispatch box as `floor_f64(min_x).to_i32() - 2` etc. Natively that
box became `(0,0,2,2)`, so the rotated tile and the fractional bar of corpus
case 02 were never painted. The GB10 worker then failed with
`Engine2D corpus case 02 edge oracle mismatch` (exact_mismatch=18288,
edge_max=219). The same pattern is in `_engine2d_draw_ir_strict_vulkan_fractional_pixels`.
Both now bind typed f64 locals first. About 20 other `floor_f64/ceil_f64(...).to_iN()`
sites remain in `src/lib` and `src/app`, along with any `<f64 call>.to_iN()`.

## Real fix

The seed lowering of builtin numeric conversions has to use the call
expression's resolved return type (f64 → float-to-int conversion), not an
integer bitcast. Add a native/JIT spec that runs the repro above. Once the
compiler is fixed, remove the workaround comments in `draw_ir_adv.spl`.

## Root cause (2026-11-23)

Seed Cranelift backend, at the call result. User functions return floats
through a uniform i64 ABI: the callee bitcasts its f64 (or the promoted f64 of
an f32) into an i64 register. `build_vreg_types` (`codegen/instr/body.rs`)
types the caller's dest vreg from the callee's declared return type (`F64`),
but the Cranelift VALUE in that vreg stayed the i64 carrier. Every consumer
then had to bitcast it back itself; `compile_binop` and call-argument
adaptation do, the builtin-method lowerings did not:

- numeric casts (`compile_builtin_method` in `instr/methods.rs`,
  `try_compile_builtin_method_call` in `instr/closures_structs.rs`) decide
  float-ness from the Cranelift value type, so an i64 carrier took the integer
  arm: `ireduce` for `to_i32`/`to_u8`/..., identity for `to_i64`. That is
  exactly `.to_i64()` == `0x4047800000000000` and `.to_i32()` == its low 32
  bits, 0;
- the scalar-float intrinsics did the same: `f(x).abs()` cleared the sign bit
  of the integer bit pattern, `.sqrt()` took the root of the bits as an
  integer, and `.floor()`/`.ceil()`/`.round()`/`.max()`/`.min()` fell through
  to a `f64.floor` function lookup and failed (`function not found`, or a
  denormal from the native binary).

A typed or untyped local hid it because the store/load round trip yields a real
f64 value; `as i32` hid it because it is a MIR `Cast`, not a method call. The
same decode already existed for cross-block floats (`sync_vars_to_vregs`,
bug `jit_cross_block_float_cast_reads_f64_bits_as_int_2026-10-05`); call
results inside one block never got it.

A second gap on the same path: `build_vreg_types` stamped the dest of
`to_f64`/`to_float` but not `to_f32`, so `f(x).to_f32()` was untyped and a
chained `.to_i64()` (or `* 2.0` then `.to_i64()`) took the
`rt_to_int_dynamic` route and returned the bit pattern; the bound-local form
`val y = f(x).to_f32() * 2.0; y.to_i64()` died with SIGILL.

HIR/MIR typing was not involved: the MIR was already right
(`Call local_floor -> v4; MethodCallStatic f64.to_i32 v4`), and the receiver
vreg was already typed f64.

## Fix

- `decode_float_call_result` (`codegen/instr/body.rs`), run after every
  instruction: for `Call`/`InterpCall`/`IndirectCall`/`MethodCallStatic`/
  `MethodCallVirtual` whose dest is typed `F64`/`F32` and whose value is an
  i64 carrier, bitcast it to f64 (and `fdemote` for f32) — the same decode
  `sync_vars_to_vregs` applies to cross-block floats. All consumers then see a
  native float, so the fix is not per-method. Cross-block sync re-encodes it
  through `def_var_coerced`, as for any other float.
- `build_vreg_types` stamps `to_f32` dests `F32`.

A first, consumer-side version (bitcast inside the two cast lowerings only)
fixed `.to_iN()` but left `.abs()`/`.sqrt()`/`.floor()`/`.max()` broken; it was
replaced by the producer-side decode.

Not changed: the optional LLVM backend (`codegen/llvm/emitter.rs`) — not built
by default and not buildable on this host; unverified. The pure-Simple
compiler lowers these conversions to MIR `Cast` from the call's typed local
(`50.mir/_MirLoweringExpr/method_calls_literals.spl`); not verified at runtime
because no pure-Simple binary is deployed on this host.

## Evidence

- Rust: `src/compiler_rust/compiler/tests/f64_call_result_cast_jit.rs`
  (in-process static JIT). On the base tree: `method_call_to_i32: got
  -1717986918 (0xffffffff9999999a), want 7` and `f64_call_to_f32_then_int: got
  0x4028000000000000, want 12`; with the fix: pass. The free-function rows pass
  in this harness even on base; that shape is red only through `simple run` /
  native-build, which the spec covers.
- Simple: `test/03_system/compiler/native_f64_call_result_cast_regression_spec.spl`
  compiles a program as a child process through `run` (JIT) and
  `native-build`. Base seed: 0/2; fixed seed: 2/2.
- 25-row matrix (scratch `matrix.spl`: abs, sqrt, floor, ceil, round, max,
  min, to_string, interpolation, unary minus, compare, pass-as-arg, to_f64,
  `[f64]` element, struct field, dict value, `f64?` unwrap, extern `-> f64`,
  lambda, parsed text, to_u16/i8/i16/u64/f32): fixed-seed JIT and native output
  equal the interpreter on every row except `g(70000.5).to_u16()` (interpreter
  saturates to 65535, compiled wraps to 4464 — out-of-range narrowing
  semantics, the same with a bound local, not this bug; filed as
  `compiled_float_to_narrow_uint_wraps_or_traps_vs_interpreter_saturates_2026-11-23.md`). On base, 11 rows were
  wrong (bits, `function not found`, or denormals).

## Remaining workarounds and sites

The typed-local workarounds in `draw_ir_adv.spl` (PR #11037) stay: the GB10
worker is built by an already-deployed seed
(`~/.cache/cargo-target-wr-gpulink/release/simple`) that does not have this
fix. Remove them once that seed is rebuilt from a tree containing it.

The 15 sites that become correct with the fix and need no rewrite (2026-11-23 grep,
`(floor|ceil|round|trunc)[_f64|_f32](...).to_[iu]N()` in `src/lib`, `src/app`):
(the two `draw_ir_adv.spl` boxes already bind typed locals since #11037),
`browser_engine/style/animation.spl:255`,
`browser_engine/simple_web_html_layout_renderer_compose_support.spl:662`,
`common/math/statistics.spl:222,237,288`, `common/math/financial.spl:643`,
`skia/feature/shaper/shaper.spl:739`,
`app/office/sheets/formula.spl:1925,4515,5245,5262,5277,5402,5965,6251`.
Any other `<f64-returning call>.<method>()` is covered the same way.
