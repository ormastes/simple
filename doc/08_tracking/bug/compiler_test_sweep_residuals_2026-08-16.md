# Compiler test sweep residuals — 2026-08-16

Triage of unfixed failures from the 2026-08-16 compiler test sweep. Engine:
`bin/simple test` (tree-walk interpreter path). One item was a stale spec and is
FIXED in this change; everything else is filed here with root-cause notes.

## Fixed in this change

- **lexer_intensive_spec: `#[` no longer emits TOK_HASH_LBRACKET** — intentional
  migration: commit `b2fbb38fc6f7` "refactor: unify tag system — merge #[]
  attributes into @ syntax". The lexer (`src/compiler/10.frontend/core/lexer_struct.spl:1384`)
  now treats every `#` as a comment start. Spec updated to assert `@test` emits
  `TOK_AT` and that `#[test]` emits no `TOK_HASH_LBRACKET`. `TOK_HASH_LBRACKET`
  still exists in `tokens.spl:211` (exported) but is dead — candidate for removal.

## Filed: interpreter gaps (unit, `test/01_unit/compiler_core/`)

All fail as `expected false to equal true` — the interpreter feature under test
is absent or returns the wrong shape, not a flaky harness.

1. **while finite-iteration guard** (`lang_basics_spec.spl`, 2 examples: while
   statements and while expressions). Interpreter does not enforce/report the
   finite-iteration guard the spec asserts.
2. **receive/after-timeout parsing** (`receive_spec.spl` "should parse receive
   arms and after timeout arms"). Parser/interpreter path for `receive ... after
   <timeout>:` arms does not produce the expected arm structure.
3. **match-exhaustiveness warning** (`exhaustiveness_spec.spl` "should keep
   interpreter match warnings on no matched arm"). Interpreter no longer emits
   (or the harness no longer surfaces) the no-matched-arm warning.
4. **nested-optional nil** (`branch_coverage_30_spec.spl` "optional - all nil
   levels"; `branch_coverage_35_spec.spl` "optional of optional - nil inner").
   `Option<Option<T>>` with nil inner/outer levels evaluates incorrectly.
5. **pipe to placeholder-lambda in parens** (`parser_pipe_operator_spec.spl`):
   `expected <lambda> to equal 15` — the parenthesized placeholder lambda is not
   applied by `|>`; the lambda value itself leaks through unevaluated.
6. **string-interpolation segment count** (`parser_intensive_spec.spl` "parses
   strings with and without interpolation"): `expected 3 to equal 34` — segment
   splitting returns a wrong count/shape.
7. **Option with unknown inner type tag** (`parser_spec.spl` "parses Option with
   unknown inner type"): `expected 300 to equal 14` — type node gets an
   error/unknown tag (300) instead of the Option tag (14).
8. **module-level pseudo-decl arena OOB** (`parser_spec.spl` "parses
   module-level expression as pseudo-decl", plus "parses a mixed module"
   `expected 7 to equal 6`): module-level expression is not wrapped as a
   pseudo-decl; downstream arena index read goes out of bounds.

## Filed: integration backend failures (`test/02_integration/compiler/`)

From `B_compiler_02_integration.log` (457 total, 55 failed). Toolchain presence
checked on this host: ghdl, llc, clang ARE installed — none of these is a
missing-toolchain environment failure; all are real defects, in two families.

- **vhdl_backend_e2e_spec.spl (20 passed / 21 failed)** — two causes:
  (a) real VHDL backend defect: `CompileError(phase: backend (vhdl), message:
  VHDL combinational local 'arr_sig' must be a fixed scalar or record)` — array
  locals in combinational context are rejected; (b) `semantic: unknown extern
  function: rt_process_run_capture` — the interpreter running the spec lacks the
  process-capture extern, so simulation-run assertions cannot execute
  (environment/runtime-binding gap, not a VHDL defect).
- **advanced_types_spec.spl (2/10 failed)** — child `Process exited with code 1`;
  compiled-program smoke tests abort. Needs per-example rerun for exact diag.
- **llvm_backend_e2e_spec.spl (20 passed / 6 failed)** and
  **llvm_parity_spec.spl (3 passed / 4 failed)** — same root cause family:
  `semantic: method 'with_cpu_override' / 'with_llvm_ir' / 'with_assembly' /
  'with_compile_time' not found on value of type object in nested call context`.
  This is the known erased-receiver method-chain limitation (builder chains on
  values whose static type was erased) hitting the specs' CompileOptions-style
  builder — an interpreter method-resolution defect, not an LLVM codegen one.
- **wasm_e2e_spec.spl (0 passed / 4 failed)** — `semantic: function
  'CompileOptions' not found` (x3): the spec's constructor-call form for
  CompileOptions no longer resolves under the interpreter; all four examples die
  in setup before any wasm is emitted.

## Unblock conditions

- Interpreter items 1–8: implement the missing behaviour in
  `src/compiler/10.frontend/core/interpreter/` (each spec names the exact
  assertion); specs stay RED per testing.md — do not weaken.
- Backend: fix erased-receiver builder-chain resolution (unblocks llvm_e2e,
  llvm_parity, likely wasm_e2e's `CompileOptions`); add
  `rt_process_run_capture` extern binding for the test interpreter; VHDL array
  combinational-local support is a genuine backend feature gap.
