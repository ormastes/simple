# Native return-only generic optional nil execution crashes

The explicit-call-types compiler candidate builds the return-only fixture
`test/fixtures/compiler/explicit_return_only_call_types.spl` with one generic
function, two call sites, two specializations and zero unresolved calls.
The ARM object is EM_AARCH64 (183). The native executable also builds, but
execution exits -11 without success output, with SIGBUS/SIGSEGV at address
0x3. It calls `absent<i64>()` and `absent<text>()`, both returning nil in a
T? context, then compares each result against nil. The later comparison-chain
control and success marker were not reached.

Evidence: `build/native_probe/explicit-call-types/return-only-arm-result.json`,
`return-only-arm-k1.log` and `return-only-arm-exec-build.log` in the isolated
compiler candidate checkout. The producer includes the canonical K1 composition
and bound runtime and builds 1217 modules without failures.

This is a native runtime/optional representation failure after monomorphization,
not an E-MONO-032 or a passing native regression. Its exact root cause is not
yet established. Preserve the compact generic syntax and failed fixture; inspect
optional nil MIR, generated return/call ABI and comparison representation. Do
not replace the fixture with a passing constant-return control or claim ARM
execution from object emission. RISC-V execution is independently unqualified.

## Root cause and candidate repair

Native disassembly exposed specialization definitions named `T` and `integer`
instead of their mangled names. Monomorphization reserved fresh IDs above
function IDs only, although locals and type parameters occupy the same symbol
table. Generated functions collided with those rows, and MIR resolved a nil
local as an indirect callee at address 3.

The candidate reserves IDs above every existing table row and registers each
specialization as a function in its owning symbol table. The rebuilt native
compiler reused 1214 modules, compiled 3, and reported zero failures. The
unchanged fixture now executes on ARM with exit 0 and exactly
`EXPLICIT_RETURN_ONLY_CALL_TYPES_PASS\n`; evidence is
`return-only-mono-symbol-result.json`. The repaired producer also emits an
EM_RISCV (243) object (`return-only-riscv-symbol.o`). This verifies code
generation, not RISC-V execution or the full bootstrap gates.
