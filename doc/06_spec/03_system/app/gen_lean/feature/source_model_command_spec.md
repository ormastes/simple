# Source-to-Lean public command

Requirements: EE-01, REQ-MC-007, C2; composition review finding EE-COMP-02.
Executable specification:
`test/03_system/app/gen_lean/feature/source_model_command_spec.spl`.

**3 scenarios authored; all UNRUN.** This companion is manually maintained,
not an execution report. No command process, compiler, bootstrap binary,
Lean checker or proof replay was launched while authoring this revision.

The scenarios call the existing `app.io.process_ops.process_run_timeout`
facade with `./bin/simple gen-lean source-model FILE TARGET`, using argv
entries rather than shell interpolation. The maintained command path is
`cli_gen_lean` → `cli_run_file("src/app/gen_lean/main.spl", ...)` →
`delegate_gen_lean` → `./bin/simple run
src/compiler/90.tools/verify/source_model_v1.spl FILE TARGET`. No dispatcher
is copied, injected or replaced and no subprocess success is fabricated.
This extends the established gen-lean process-testing approach to the public
command route and real worker delegation.

| Scenario | Action | Required observation |
|---|---|---|
| Enum file through dispatcher | Run the public command on a checked exclusive regular file with a space in its basename | Exit 0, empty stderr, NOT_CHECKED header, exact source digest and target, cfg receipt fields, both named variants and i32 constants, no raw enum helpers or PASS claim |
| Explicit target forwarding | Run the same target-conditional source for x86_64 and aarch64 | Both exit 0; each model names the requested target and contains only its selected constant |
| Atomic worker failure | Run a valid enum function followed by an unsupported f64 function | Exit 1, export diagnostic on stdout as the existing dispatcher forwards it, empty stderr, and no header or partial Lean model on either stream |

Every invocation allocates its own `secure_temp_dir(".", "ee-model-cli-")`,
checks `file_create_exclusive` and `file_is_regular_no_follow`, and removes
the owned directory before returning captured output. Cleanup failure or a
remaining directory returns a test error. Setup failure also attempts
cleanup. The outer process has a 45-second deadline; the maintained worker
delegation retains its existing 30-second deadline. A timeout or missing
executable cannot satisfy either expected exit status.

Execution requires a separately qualified current self-hosted `./bin/simple`,
the normal library environment, and the tested repository as the working
directory. The authoring checkout has no `bin/simple`; there is no fallback
to a Rust seed or another checkout. Process-wrapper availability, actual
argument forwarding, export success, timing, and cleanup remain unverified
until the scenarios are authorized and run. Even a future pass establishes
command behavior and unchecked artifact generation, not Lean kernel
acceptance, native equivalence, or release readiness.

The separate worker manual at
`doc/06_spec/01_unit/compiler/verify/source_model_v1_spec.md` accurately labels
in-memory worker checks and successful/refused real-file command API cases.
