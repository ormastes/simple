# Preserve explicit OS build compiler identity

**Manual draft; execution and docgen TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_compiler_selection_v1_spec.spl`.
Requirements: platform REQ-001 and REQ-016.

Choose distinct `SIMPLE_BINARY` and `SIMPLE_BIN` values. The production policy
must retain the primary value, use the alias only when the primary is absent,
and return no explicit value when neither was supplied. A missing explicit
compiler or missing canonical admission root must return an empty selection;
these unit cases do not establish executable compiler admission.

The live CLI-route suite supplies the separate positive acceptance gate: a
real Stage4-provenance-admitted compiler must win over a different alias, and
actual OS builds must use its pinned identity. Installed Rust seeds are not
part of implicit discovery. Invalid explicit provenance must fail closed.

Existing `simpleos_compiler_admission_spec.spl` tests backend capability with
unit shims, including rejected seed banners and nonworking canaries. Those
shims are not provenance receipts or live CLI evidence.
