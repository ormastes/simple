# UFCS Propagation Experiment 2026-04-18

## Setup
- Started from: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
  mtime: 2026-04-17 12:26 (pre-experiment baseline)
- Modification: `src/compiler/35.semantics/resolve.spl:572` — partial unstub;
  `resolve_methods` now creates a fresh empty `SymbolTable` and invokes
  `MethodResolver.try_ufcs` (free-function dispatch with receiver as first arg)
  instead of returning early with an empty error list.

## Results

| Generation | Stub symbols | Stub functions | Ambiguity warnings | UI001 lint test |
|---|---|---|---|---|
| Stage 4 | 325 | 2419 | 153 | FAIL (Runtime: Function 'level' not found) |
| Stage 5 | 325 | 2419 | 154 | FAIL (Runtime: Function 'level' not found) |
| Stage 6 | 326 | 2420 | 154 | FAIL (Runtime: Function 'level' not found) |

## Conclusion

The unstub did not reduce stubs across generations: counts stayed flat at 325/2419
(Stages 4–5) and actually ticked up by 1 at Stage 6 (326/2420). Ambiguity warnings
rose from 153 → 154 at Stage 5 and held at 154 at Stage 6. This indicates the UFCS
free-function dispatch path is now active and exposing additional duplicate-method
ambiguities in the compiler's own type-inference module (`HmInferContext`), but the
de-duplication logic that would collapse them has not yet landed. The one-stub
increase at Stage 6 (`CompilerDriver_dot_compile_to_native`) is a secondary effect
of a different duplicate-definition collision surfaced when the richer resolution
context expands the visible symbol set. UI001 never fired: the `lint` subcommand
itself panics on `Function 'level' not found`, a stub-generated runtime error
unrelated to UFCS dispatch.

## Next steps

UI001 firing requires two pre-conditions that are not yet met:

1. **De-dupe blocker** (tracked in `doc/05_design/compiler_rfc_ufcs.md`): the
   ambiguity-refusal logic must be upgraded to a preference rule that picks the
   UFCS free-function candidate when exactly one free-function and one instance
   method share the same name, instead of refusing both.
2. **`lint` stub fix**: `Function 'level'` and `Function 'line'` must be un-stubbed
   (or the duplicate-definition collision in `CompilerDriver` resolved) so that the
   lint subcommand can actually execute past its initialization phase.

Until (1) is in place, adding more bootstrap generations will not change the
outcome: stub counts will remain ≥ 325 and ambiguity counts will stay ≥ 153.
