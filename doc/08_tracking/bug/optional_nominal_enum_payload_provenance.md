# Optional nominal enum payload provenance

Status: narrow native repair verified; general generic/nested optional provenance and full-host qualification remain open.

## Actual failure

A source-matched pure bootstrap parent rejects `Packet.Hold(Some(value))` when `Hold` expects `Payload?` and `value` is an instance of that exact nominal `Payload`. The diagnostic is a payload type mismatch. A tiny control constructing `Hold(nil)` compiles, links, and runs successfully. A second owner defining a different `Payload` with the same spelling is correctly rejected.

The baseline uses compiler `bd86d7aceeb0e0de2dfb55b0bf3fdafc837c05b2bbea5c101e9ea14c8024e0f3`, with genuine canonical parent verification and matching runtime binding before and after. Evidence is `.simple/storage/build/phase3-mir-owner-scratch-cycle2-20261016/optional-payload-result.json`, SHA256 `98a56908bc626d27d8dd80bd66c9456abed292f2fb3591821512d46968293b29`. Its supervised run ended quiescent at 523788 KiB peak. The owned-Some case failed compilation; the nil runtime oracle and foreign-owner rejection passed. This is bootstrap-parent native evidence, not SSpec or full-host qualification.

## Ownership boundary

The named `Some` constructor tags its runtime enum handle, but retains an `Optional(inner_type)` witness only for primitive inner types. A proven nominal payload therefore loses its semantic owner before the containing enum validates its optional field. The validator correctly refuses an opaque handle without matching type evidence. The fix must retain genuine nominal provenance at the producer, preserving the existing rejection of unrelated owners and unknown or unresolved types. It must not admit arbitrary opaque integers or waive payload validation.

The narrow producer change retains a nominal witness only for an existing Struct, Class, or Enum declaration with zero type arguments. Parameterized and nested payloads keep their prior behavior; this repair does not claim their support. General closed-generic optional provenance remains a separate follow-up.

The first diagnostic in the larger compiler-closure probe is the corresponding `HirExprKind.Return(Some(value))` construction. That larger attempt also has other diagnostic families and exceeded its 8 GiB limit before native output. This small reproduction does not establish that correcting optional provenance resolves every larger error or the memory limit.

## Verification boundary

The native acceptance criterion requires the changed producer to compile and run the owned-Some fixture with its actual payload value, and reject the foreign-owner fixture. The foreign negative must run again because retaining a new witness can affect nominal compatibility; the unchanged nil control retains its original PASS. Authored SSpec execution, the larger scratch/token assertions, full-host admission, and required compiler/core/MCP checks remain unqualified or unrun. No passing result is inferred from source review.

## Final changed-producer result

The final producer `e4ae5676596a63dcb4d390835304b656710e0575756d72831f8c7e63a7f74068` compiled, linked, and ran the owned-Some fixture with exact output `optional-owned=41` and empty stderr. The foreign same-name owner still fails compilation with exactly one enum payload mismatch and no executable. The unchanged nil control retains its baseline PASS without replay.

Evidence: `.simple/storage/build/phase3-mir-owner-scratch-cycle3-20261016/optional-payload-result.json`, SHA256 `527e7fd093712b732be235e15b1fc75414af452b46111ee27b80fe037f7269b9`. Both canonical runtime-binding calls returned zero with identical output; compiler, admission, parent receipt and fixture hashes remained stable. The actual resource owner ended with exit zero, quiescent and no escaped process, at 524396 KiB peak in 31.1 seconds. The executed binary SHA256 is `01bdf62970aff4b0baf71e196501c6b8b906de663ed1dcb8b8d58c4305171706`.

This completes the narrow native optional-owner criteria within the third and final producer cycle. The full matrix still stopped at its explicit 60-second diagnostic deadline; there is no general-host admission. The earlier 414-module scratch/token probe exceeded its memory cap and was not replayed. Its assertions, runtime SSpec execution, required core/MCP checks, and physical-memory target remain unqualified or unrun. No broader completion or release PASS is claimed.
