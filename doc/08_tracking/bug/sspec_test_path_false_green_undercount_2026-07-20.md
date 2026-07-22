# Bug: `simple test` false-green undercount (test-path miscompile)

Status: OPEN — root-cause fix in progress (lane active)
Observed: 2026-07-20 · Filed: 2026-07-21
Severity: P0 — deploy blocker; invalidates `simple test` verdicts on the self-hosted binary

## Symptom
Self-hosted native binary only. `simple test <spec>` executes/reports a PREFIX of
the spec's declared `it` examples while claiming success:

- `test/01_unit/app/arch_check_spec.spl`: 74 declared → `Results: 18 total ...
  All tests passed!` with `--clean` (FALSE GREEN, exit 0); 66 warm.
- `test/01_unit/compiler/bitfield_sugar_spec.spl`: 28 declared → "no parseable
  pass/fail summary in test output; refusing synthetic pass" → 1 total, 1 failed
  (honest fail, different breakage of the same path).

`simple run <spec>` is correct on ALL backends (JIT / `--interpret` /
`--interpret-optimized`): 74/74 and 28/28. The defect is exclusively in the
`test` command path.

## Root cause (instrumented diagnosis; fix in progress)
Disproven: test-runner logic bug, output-capture truncation, parse-source bug,
symbol collision, interpreter-backend abort. strace shows the child emits all 74
result lines and the parent captures them all.

Established: compilation-context-sensitive **native-build (Cranelift AOT)
codegen miscompile**. The identical result-parsing code
(`run_test_file_interpreter` → `parse_test_output` path) computes 74 when
compiled in a minimal closure but 18 inside the full CLI closure. It is
input-byte-sensitive (a stderr warning-length delta flips it), which is why
warm (66) differs from clean (18). Dispatch path proven:
`run_test_cli` → sequential → `run_single_test` → `run_test_file_interpreter`.
`--parallel`/`--fork` are separately broken (1/0 reported).

## Arch coverage (2026-07-21)
- x86_64-unknown-linux-gnu: REPRODUCES (baseline above).
- i686 / armv7 / riscv32: full CLI is not a supported frontend target — filed as
  an honest gap, not claimed coverage.
- aarch64 / riscv64: fixture-level cross checks behaviorally identical to
  x86_64; full-CLI verification under qemu in progress.

## Prevention (guard, NOT a substitute for the root fix)
`scripts/check/check-sspec-count-truthful.shs` — compares the STATIC declared
`it` count against the runner-REPORTED `Results: N total`. Fail-first validated:
fails arch_check (74≠18, FALSE-GREEN label) and bitfield (28≠1, MISMATCH label)
on the affected binary. Run per-arch via `SIMPLE_BIN=<binary-or-qemu-wrapper>`.
