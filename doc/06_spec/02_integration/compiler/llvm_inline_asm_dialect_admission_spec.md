# Real LLVM inline assembly object contract

Status: authored manual expectations; runtime UNRUN. This is not generated execution evidence.

Executable: `test/02_integration/compiler/llvm_inline_asm_dialect_admission_spec.spl`.

The production owner is `src/compiler/70.backend/backend/llvm_backend_tools.spl`. Both the byte-returning and cache-publication APIs reject an LLVM error diagnostic even when llc exits zero, before reading or publishing the partial object. Nonzero status remains an error. Warnings that quote an error message stay admissible.

Required real-tool checks: bare Intel assembly under the existing default AT&T dialect and a malformed explicit-Intel instruction return an error. Fresh destination paths remain absent. Valid explicit Intel produces port bytes EE/EC, 66 EF/66 ED, EF/ED at disassembled instruction boundaries in the named symbol. Valid AT&T retains EE. An explicit Intel block restored to AT&T must retain TWO EE instructions, proving the following assembly survived restoration. Privileged instructions are never executed. Missing llc or an admitted objdump is a failing prerequisite, never a passing skip.

Limits: these IR-level integration cases exercise the real object compiler, not source frontend/MIR constraint lowering or actual hardware. Authoritative actual-source-owner object reproduction (including io_wait), producer qualification, assembly dialect transport, LLVM-lib diagnostics and full runtime validation remain outstanding. The six workaround tags stay active.

## Cycle 2 review correction (runtime UNRUN)

The parser is now `src/compiler/70.backend/backend/llvm_diagnostic_admission.spl`; the two production APIs supply the exact resolved llc path and actual compile-input path. It recognizes optional producing-tool prefixes, exact input/pseudo-file origins, numeric line/column positions and severity. A located diagnostic with a column consumes its following raw source line. Unindented `.warning "example: error: text"` and a warning source label beginning `error:` are accepted. Tool-prefixed genuine errors are rejected.

The integration spec additionally requires a valid warning-producing object from the byte API and a successfully published, disassembled object from the scalar path API. It uses the existing `find_objdump_portable` owner: objdump is not a sealed native-tool role. Exact resolved tool paths and binary/version/source provenance must be pinned during a future authorized qualification run; none are invented here.

An actual-tool observation precedes invalid-assembly API checks. The captured tool result distinguishes an observed zero exit plus missing port instruction from a nonzero tool status. The latter cannot qualify the zero-exit branch. No synthetic llc or new test toolchain is introduced. All these runtime paths remain UNRUN; qualification HOLD remains in force.

## Final cycle 3 (runtime UNRUN)

LLVM's DiagnosticPrinter suppresses the inner severity label when the handler has printed an outer severity. The final parser recognizes the trusted origin and numeric location with its `: ` terminator independently of that inner label. The outer severity remains authoritative. Source echo is consumed only when both line and column are present, including a blank or non-ASCII line; no caret is required. Filename-only, line-only and unlocated warnings leave the next actual diagnostic visible. Both printer modes and next-error controls are explicit unit cases. The real byte API and published-path API both include a labeled `.warning` object and named-symbol disassembly.

The malformed-mnemonic fixture requests no port instruction. Its zero exit, if observed, is labeled `EXIT_ZERO_ASSEMBLY_ERROR_NO_PORT_LOSS_ORACLE`; absence of `ee/out` is not instruction-loss evidence. Only the actual bare-Intel port fixture may establish a zero-exit partial-object observation. Producer-specific child status/diagnostics/object must still be bound to each API invocation during authorized qualification. All runtime evidence remains UNRUN and qualification HOLD.
