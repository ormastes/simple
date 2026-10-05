# Proven array mutation methods missing from pure-Simple MIR dispatch

Status: source repair prepared; native regression UNRUN.

The Cranelift Phase2 producer `776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`
compiled the generator/verdict tools against source `9737d1217bc44439b56bba6c2ef16faaff51bd20`.
Both passed HIR then failed MIR: captured generator diagnostics include 103 clear,
17 pop and 2 sort calls; verdict includes one sort. These are diagnostic-line
counts, not test counts. No subsystem test binary was produced by that attempt.

`is_mutating_method` already listed these methods, but the unresolved builtin
array dispatch did not implement them. This repair requires a proven runtime
array receiver and zero arguments. It retains the existing receiver evaluation
and indexed/field writeback mechanism. Unknown or custom receivers and invalid
arities still take the existing resolver/error path.

`rt_array_clear` returns an internal I8 status; Simple clear returns the array.
`rt_sort` mutates and returns the same array handle, with signed-number/text
ordering. Its `rt_array_sort` compatibility wrapper returns bool and is unsuitable
as the expression result. Both repaired routes return the original MIR local,
preserving array and element metadata.

Pop first uses the existing typed last/Option construction, then removes the
element through `rt_array_pop` and writes back the stable receiver. The empty
branch remains None rather than decoding nil into Some(0); unknown element types
are not guessed. This deliberately reuses the first/last element decoding owner.

`test/04_smoke/native_array_mutation_methods.spl` has 20 authored checks for
signed/text ordering, result values, negative/zero/false/text pop, empty arrays,
wide boxed i64 pop, byte-array operations, value-copy isolation, and field/index
mutation with once-only receiver evaluation. This does not establish ordering
for large unsigned integers. It must be compiled
by a repaired pure-Simple producer and executed. A Rust seed compiling this
fixture does not verify this MIR repair. Actual registered/executed counts are
pending. Separate Result predicates, enum construction and type-transport
failures from the helper build remain unresolved by this change.

The separately completed LLVM-codegen helper attempt using the same producer
and source captured the same 181 generator and 47 verdict MIR error lines and
identical method counts. Both backend logs explicitly contain truncated stderr;
these counts are not an exhaustive compiler diagnostic inventory. Generator log
SHA-256: `84643a0655433a9a60c3f4d6debd92017ec3a9f37a289418a3ae10a4f5b2e578`;
verdict: `73355091f3976ff2c152a1e6cbed055d54582d110194d030e18ea140018e7cbb`.

## Packed-byte representation remains an open correctness boundary

Core-C `runtime_native.c:8366` returns raw 0..255 for
`RT_CORE_ARRAY_FLAG_BYTES` in `rt_array_get`; ordinary array slots are tagged.
The existing first/last/get helper calls `decode_runtime_value`, whose narrow
integer branch shifts by three. Reusing that helper for pop does not fix this
pre-existing decoder mismatch. `rt_sort` likewise compares values read through
`rt_array_get` with its tagged comparator. A `[u8]` literal fixture alone does
not prove the packed storage route was selected. Runtime qualification for
packed-byte pop/sort is explicitly pending and must not be inferred from
ordinary tagged-array success. The existing `rt_array_is_byte_packed` ABI can
distinguish storage for a subsequent representation-aware repair. No check has
been disabled, and this source checkpoint is not an admitted runtime candidate.
