# Enum match with all returning arms manufactures an implicit return

Status: OPEN; source repair and SSpec prepared, all verification UNEXECUTED.
Requirement: REQ-MIR-ENUM-MATCH-DIVERGENCE-001.

## Evidence and scope

Frozen fullCLI source acdc14ec496 fails `app.office.sheets.formula._a_value_of`
with a Cranelift return operand i64 against f64 signature. Pinned producer SHA256:
ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a.
Its receipt records HEAD480622a793b67a55ac2c364b313778229c024f75 plus dirty-source
fingerprint; committed HEAD alone is not complete producer provenance.

Independent diagnostic budget is exhausted (4/4 including two setup failures).
Admitted imported and local bare-arm extractions both failed codegen in
main._a_value_of. Neither retained operand-level MIR; exact equivalence to the
original verifier error remains an inference. Diagnostic source/receipt roots:
/home/yoon/dev/simple-float-option-physical-20261106/build/cellvalue-imported-bare-attempt3
and sibling cellvalue-local-bare-attempt4. They use core-c-bootstrap/wholeprogram1;
fullCLI used host-gpu/two-pass. No qualification claim follows from these diagnostics.

## Concrete source defect

At the pre-fix switch_operators_calls.spl:5049/5397, explicitly returning arms
correctly skip merge copies/edges. But5417 unconditionally opens ematch_merge;
5423 fills its result with i64 zero when result_defined=false. Ordinary f64
function lowering uses lower_block(nil expected type), returns the synthetic
local from its tail, and sees an unterminated block at function_lowering.spl:1094.
It can emit a new implicit return at1163 with that i64 operand. Correct f64 enum
payload decoding cannot prevent this unrelated synthetic return.

These match and return paths are identical between the producer receipt HEAD and
frozen source; function_lowering differs elsewhere only in a UFCS check. HIR
scopes/variable IDs separate the same-named `value` binders; no name-overwrite
repair is proposed. Physical-float optional classification PR7299 is independent.

## Design and implementation

Track actual incoming merge edges at the normal-arm, guarded-default, and final
fallthrough/default Goto emission sites. A live Unit arm contributes an edge even
without a result, so result_defined is deliberately not used as reachability.
After existing semantic capture completes, if no merge edge exists and the current
block is explicitly terminated, retain that current block and return the reserved
unused result identifier. Do not activate the orphan merge or fabricate zero.

The orphan block retains its initial Unreachable terminator (backend trap). Calling
terminate_unreachable after switching would not suffice: the builder's explicit
termination query treats Unreachable as its unfinished-block sentinel.

Propagate child termination in lower_block_expected before optional boxing/type
registration, and in both let-initializer lowering paths before coercion/binding.
This prevents consumption of a reserved but never-defined result. No global
builder semantics, enum payload semantics, or spreadsheet syntax are changed.

## Acceptance and validation

New executable SSpec: test/01_unit/compiler/50.mir/enum_match_divergence_spec.spl.
It lowers real frontend/HIR/MIR and checks function presence, MIR errors, return
operand types/counts, and live merge blocks. Eight scenarios cover all-return f64,
mixed early-return/live value, all-return Unit, live valueless continuations,
optional tails, optional let initializers, nested all-return matches, and a live
guarded catch-all beside returning arms. The shared oracle calls the exported
mir_verify_module API and rejects MIRV-005e (read-but-never-defined local) across
instruction operands and terminators, catching hidden boxing/copy uses even when
return counts/types remain correct. Guard syntax follows the existing
match_guard/match_guard_invariant_acceptance_spec.spl fixture.
Parser acceptance for these new fixture strings is UNEXECUTED, not assumed proven.

Source diff reviewed; all compiler, SSpec, native, broad compiler/lib/MCP checks,
coverage measurement, and generated-manual validation remain UNEXECUTED. No fifth
diagnostic attempt or qualification retry is authorized. Qualification5/6 remains
unchanged. No commit or PR has been made for this repair.

Risks requiring eventual execution: semantic-capture behavior around orphan merges;
backend/SSA handling of unused reserved locals; guarded catch-all and non-exhaustive
match paths; native optional/initializer termination. Arbitrary expression operands
that themselves return (beyond audited block-tail and let paths) are not newly
claimed supported by this scoped repair. Independent sibling work must stay isolated.
