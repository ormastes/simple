# C1: resolved source calls never reached the manifest finalizer

At release d9e177de79ac599ecd4b165e39c26d99f037c357, verification_call_manifest_finalizer.spl accepted positional resolver captures, but production lowering had no capture producer or invocation. Lower_call_with_value retained real Var/NamedVar SymbolIds until its textual MIR Call emission, then discarded the selected identity. Hand-authored manifest specs were not source-compiler integration.

The repair adds an opt-in source-calls command and actual HIR/MIR capture producer. Unknown boundaries fail closed, complete final MIR is bound before publication, and ordinary lowering remains unchanged. The existing finalizer and manifest validator are reused without weakening their signature/body checks. Input symbol environments are copied because ordinary default/provider lowering can register or replace symbol rows.

Public regressions cover real frontend calls, ordered signatures, nested/default positions, stale final MIR, malformed source authority, failed publication, owner isolation, target binding and actual CLI dispatch helpers. All UNRUN; no observed runtime RED/PASS, Lean proof, benchmark or production authentication claim. Full C1/C2/C6/C7 is still open.

## C1-01: defaults were not owned by the new producer

Independent cycle-1 source review found that `lower_module` does not execute `prescan_one_function_v1`, which is the ordinary process-global defaults registration path. HIR retains supplied call arguments only. Revision 1 therefore left omitted defaults missing on a fresh invocation and could consume stale same-name global defaults on a warm invocation. Its original literal-default scenario was authored but never executed; no observed runtime pass was claimed.

Revision 2 prepares retained parameter/default rows by actual selected SymbolId, bypasses legacy default padding for the opted-in emitter, and refuses any earlier unscoped padding route before global reads. Fresh lexical frames bind already evaluated supplied/prior-default parameters, reject repeated active declaration/default-index pairs, and clear on success or refusal. The explicit 128-frame ceiling prevents unbounded recursive default expansion without prohibiting ordinary fully supplied recursive calls.

Six additional public-API scenarios cover nested default calls and ordered dataflow, sequential different defaults with failure between, real-prescan stale global contamination, full input HIR/symbol-table preservation, lexical shadowing/prior parameters, cycles and actual 128/129-frame boundaries. Total: 20 producer plus 12 unchanged CLI/API scenarios, all UNRUN. This source correction awaits targeted independent review and does not establish compiler execution or formal acceptance.
