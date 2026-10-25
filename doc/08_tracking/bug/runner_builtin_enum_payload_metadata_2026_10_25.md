# Runner builtin enum declaration metadata

Status: source repair; executable regressions authored but UNRUN.

The frozen Phase 3 runner build recorded 285 MIR modules, 223 successful and 62
failed. The retained log is
`/tmp/phase3-resume-20261025-4674/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/test_runner_build.log`.
At lines 4660 onward, named Result/Option constructors reject missing declared
payload metadata. Frozen source is `46772223a7c`; the campaign identifies the
compiler and linked runtime capsule by digest prefix `991be8`.

`register_builtin_enum_dual` published variants/discriminants/runtime IDs but
neither generic authority nor declaration payload schemas. The nongeneric
fail-closed guard in `lower_enum_construct_named` therefore rejected builtins.
Equivalent donors `fa047a3bb1f` and `7bcac7a9f66` register generic authority;
the latter records historical native red/green evidence. Neither is present
in the inspected `origin/release_phase3` base `d9f51bf4c4b`. They restore the
old generic route but leave zero/excess payloads unchecked, so were not copied
as a complete semantic repair.

The repair registers Option's T and Result's ordered T/E payload schemas and
unit None, with exact builtin authority revoked by user enum registration.
Generic builtin constructors validate declaration arity and argument names.
Expected wrapper types now cross expression and method dispatch; Result uses
the existing typed constructor, with canonical payload checking/encoding.
Option checks its declared inner type and retains typed None. Inferred payloads
require retained source/local type evidence; no Any payload is invented.
The new authority map follows nested lowerer copies and transient root promotion.

Regression scope:

- `enum_missing_payload_metadata_spec.spl`: metadata T/E ordering, all four
  constructors, zero/excess arity rejection, distinct Result T/E mismatch,
  Option payload mismatch, typed None, explicit owner shadow, actual Call
  expression expected-type forwarding, and preexisting nongeneric fail-closed
  checks.
- `builtin_enum_payload_runtime_spec.spl`: real provider/importer construction
  and extraction of integer Ok, text Err, text Some and typed None.

No compiler test, seed substitution, runner build, or bootstrap was executed.
The bounded campaign owner reports no qualified interpreter/full CLI in this
lane; the admitted compiler-only producer cannot execute these specs. A newly
built producer containing this repair must compile and execute Hello before
runner reconstruction and these tests can qualify it. This source change does
not repair or admit the frozen producer retroactively. Global compiler/lib/MCP
checks remain pending that supported producer.
