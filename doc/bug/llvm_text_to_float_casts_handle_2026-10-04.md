# LLVM text-to-float casts a string handle numerically

The LLVM-produced pure compiler built the Result-array regression but its
positive executable exited 7 at the floating-array check. Object disassembly
showed that `float_values` constructed doubles with bits `428078e4b82e0800`
and `c28078e4b8400800` instead of `1.5` and `-2.25`. Main compared these against
different huge constants for identical source literals. Array boxing and reads
used `rt_value_float` and `rt_value_as_float` correctly.

The Rust LLVM producer's `MethodCallStatic` floating-conversion fast path
treated an integer LLVM carrier as a numeric input, including a STRING-typed
runtime handle. The self-hosted parser uses
`expr_get_float(idx).to_float()`, so that error converts each literal's text
allocation address into a floating value while building user programs.

Match the existing Cranelift path for a STRING receiver: call
`rt_string_to_float`, then decode its boxed result with `rt_value_as_float`.
For f32, narrow only the decoded f64. Numeric signed/unsigned receivers keep
their existing numeric conversions. Optional parse methods are unchanged.

Focused emitter regressions check actual generated LLVM IR and verification
for all three text conversion names and genuine signed/unsigned numeric
receivers. The native fixture covers parameters, positive/negative fractions,
invalid text, zero and numeric conversions. Actual seed bootstrap/native
validation and a rebuilt pure compiler's full Result-array fixture are required
before the original Result-array verification can be considered complete.

The initial repaired-seed native fixture passed both parameter parsing checks
but exited 3 at the direct text.to_f64() comparison. Preserve float-cast
destination types in LLVM's VReg type map as well: a consumer must not select
integer comparison semantics for the unboxed float result. The focused tests
now check destination F64/F32 metadata. The first failed native receipt remains
preserved. The expanded repair passed both focused LLVM IR tests and the native Windows fixture (compile exit 0, run exit 0, expected PASS marker) using immutable seed SHA256 5885136bf66130f384b907a4b2857c21df1e3b5bf38274f9a9f911d4c2b70308. Native f32 execution remains untested; f32 lowering is covered by the IR regression. Rebuilt pure-compiler Result-array validation and full bootstrap qualification remain pending.

