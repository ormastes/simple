# mock_spec twins shadow CallRecorder/CallVerifier with a full alternate mock framework

- **Files**:
  - `test/unit/lib/common/mock_spec.spl:123,155` (625 lines)
  - `test/unit/std/mock_spec.spl:123,155` (593 lines, near-duplicate of the above)
- **Real product code**: `src/compiler_rust/lib/std/src/spec/mock.spl:308,347` —
  `class CallRecorder` (`static fn new()`, `me record(...)`) and
  `class CallVerifier` (`recorder: CallRecorder`, `method_name`, `VerifyCount`-based
  `times()`/`once()`/`never()`/`at_least()`/`at_most()`).
- **Found during**: continuation of the SHADOW-family spec vacuity sweep
  (worklist rows 87, 149, 150).

## What's wrong

Both specs declare their own `CallInfo`/`CallRecorder`/`CallVerifier`/
`StubEntry`/`Mock`/`Spy` mini-framework from scratch (`CallRecorder.create()`
not `.new()`, `calls: [CallInfo]` with `args: [i64]` only, `CallVerifier`
driven by a `count_type: text` string tag ("once"/"never"/"exactly"/
"at_least"/"at_most") instead of the real `VerifyCount` enum). This is not a
thin field-rename shadow — it is a complete second implementation of the
mock/spy/stub framework (500+ lines each) that happens to reuse two of the
real module's class names. Neither spec can ever catch a defect in the real
`src/compiler_rust/lib/std/src/spec/mock.spl`, since none of its real code
path executes.

## Why not fixed in this pass

Same class of finding as `narrowing_spec`/`riscv_dual_arch_spec`: importing
the real `CallRecorder`/`CallVerifier` would require deleting and rewriting
essentially the entire file (`Mock`, `Spy`, `StubEntry`, `ArgMatcher`
matching helpers all reference the local classes and would need to be
re-derived from the real `mock.spl` API, which also supports `ArgMatcher`,
`arg_any`/`arg_exact`/`arg_gt`/etc. matching that the local reimplementation
duplicates independently). This is a full-file rewrite, not a bounded
import-swap.

## Unblock condition

Rewrite both specs to import `CallRecorder`/`CallVerifier` (and `Mock`/`Spy`/
`ArgMatcher` if those exist in the real module) from
`src/compiler_rust/lib/std/src/spec/mock.spl`, dropping the local
reimplementation entirely, and confirm the existing assertions still hold
against the real `VerifyCount`-based verification semantics. Consider
deduplicating the two near-identical twin files at the same time.
