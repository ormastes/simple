# Retained collection type ignored by for-in dispatch

Status: OPEN; candidate source fix and regressions, native UNRUN.

Observed baseline: producer `3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`,
source `96eaa4da8783f56a3a7954399fbb83573e36afa4`, packet
`p3-object-goend96-p23bd20-1/work/attempt.uUeHUP/1`.
`src/app/bug/workaround_index.spl` compiled alone: HIR 1/1, zero generics,
then MIR rejected for-in with collection MIR type I64. Exit 1, elapsed 70s,
peak tree RSS 9,927,184 KiB, natural/quiescent closure. No object success.

The baseline diagnostic does not identify the exact loop. That module contains
text parameter iteration, split chains, array field projections, and indexing
a Result-derived text array. The native fixture preserves each form separately
from explicit-local controls; it does not claim all are demonstrated failures.

Source-proven structural defect: `lower_for_iterator` already reads a local's
declared Array/Slice HIR type to select the element decoder, but then rejects
that same collection when its MIR ABI local is I64 and its array marker is
absent. Str provenance has the analogous gap. Method-call lowering already
consults retained Str metadata, so calls and iteration can disagree.

The candidate uses retained collection metadata for dispatch only on I64
locals. It does not infer array identity from integers, Any, dictionaries, or
nominal names. Other MIR representations retain existing behavior. Text uses
the existing Unicode splitter; array elements use the existing decoder. No
new runtime allocation, handle cast, lifetime extension, or alias is added.
Extra work is one local-type lookup and scalar predicates per lowered loop.

Regression coverage: four MIR specs force absent representation markers and
check emitted array/text calls, rejection of scalar/dictionary/Any/unknown
inputs, and rejection of contradictory floating representation. The native
fixture has ten Unicode, empty, field, typed-local, Result, and owner-reuse
assertions. Neither source review nor MIR text inspection is native PASS.

Qualification pending: compile/run the fixture on both backends with the
candidate compiler, then retry the original single module and compare actual
elapsed time/peak RSS. Run the existing workaround-index behavioral specs.
Do not retire this bug or claim the original failure fixed until that evidence
exists. The live original object queue and its caches remain untouched.
