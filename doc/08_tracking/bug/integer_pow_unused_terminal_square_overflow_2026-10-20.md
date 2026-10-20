# Integer power evaluates an unused overflowing terminal square

Status: reproduced; paired repair candidate, Simple/runtime qualification pending.
Canonical bug ID: `integer_pow_unused_terminal_square_overflow_2026_10_20`.
Bug database reconciliation: pending a qualified bug tool. This dated report
retains original evidence and does not claim a resolved database entry.

## Failure and owner

The existing C intrinsic owner `src/runtime/runtime_core_intrinsics_impl.h`
and its pure-Simple counterpart `math_pow_i64` in `src/lib/common/math.spl`
square the base on every loop iteration, including after the last useful
multiplication. `pow(INT64_MAX, 1)` requests a representable result but the
unused `INT64_MAX * INT64_MAX` is signed C undefined behavior. The public
`pow_i64` alias delegates to that Simple helper.

This is separate from the previously recorded missing `__simple_pow` archive
owner. A successful link or manual owner relink does not test this arithmetic
boundary. No existing producer, archive, source snapshot or cache was modified
by this candidate.

## Original executable evidence, before the repair

Owned worktree: `C:/dev/simple-pow-terminal-square-20261020`.
Branch: `work/bootstrap-pow-terminal-square-20261020`.
The new C selfcheck links the real `runtime_core_intrinsics.c` translation
unit, not a copied implementation. LLVM clang 23, VS2022 BuildTools vcvars64,
`-O2 -g -fsanitize=signed-integer-overflow
-fno-sanitize-recover=signed-integer-overflow` were used on native Windows.

`build/native_probe/pow-terminal-square/baseline.log` records exit 1 and:
`runtime_core_intrinsics_impl.h:16:14: runtime error: signed integer overflow`.
The operands are both `9223372036854775807`; UBSan identifies the otherwise
unused base square. Baseline log SHA-256:
`2c824b3d83e16d862c14ec516de201ae15783ceaea933cd50fe35ae2e3c51e48`.

## Repair and same-mechanism controls

Both owners consume the current exponent bit first and square the base only
if another bit remains. This preserves the existing negative-exponent result
zero, exponent-zero result one, and the useful multiply/square order. It
does not define a new overflow policy for mathematically unrepresentable
results. This is a proper owner repair, not a temporary source workaround.

`src/runtime/test/rt_integer_pow_terminal_square_selfcheck.c` executes 14
controls covering signed endpoints at exponent one, a large non-endpoint base,
positive/negative multistep boundary powers, odd/even exponents, zero base,
zero/negative exponents and the maximum positive exponent on base minus one.
With the repair, the same sanitized compile/run exits 0 and prints
`PASS: 14 integer power terminal-square controls`.
Fixed log SHA-256:
`fff2197aa8c073c2afa5563e6137949ac03055e759cae22b23deca5dd93090c5`.
Executable SHA-256:
`c4941398baf9ed390f56e3c88da17be0d162a0507455ee56a6271784f1d0c7ea`.
Sanitizer-library CRT import warnings were retained; no unresolved-symbol or
duplicate-symbol force option was added. Logs and the exact build command
remain in the owned `build/native_probe/pow-terminal-square` directory.

## Unproven gates

The three scenarios in
`test/01_unit/lib/common/math_pow_terminal_square_spec.spl` call the actual
Simple helper and alias. They are AUTHORED_UNEXECUTED. A qualified general
pure-Simple runner, docgen/manual review, branch coverage, compiler/lib/MCP/LSP
checks, full runtime/core integration and non-Windows execution remain pending.
The C sanitizer pass is not evidence for these gates or for Phase3 admission.
The shared Phase4 compiler lane continues to own its live builds and caches.

Provider token usage: unavailable. Comparable cohort average: unavailable;
ratio: unavailable. No guessed usage or performance values are reported.
Final workaround/fix commit linkage is supplied by the candidate PR; the bug
must not be marked resolved until qualified verification and landing finish.
