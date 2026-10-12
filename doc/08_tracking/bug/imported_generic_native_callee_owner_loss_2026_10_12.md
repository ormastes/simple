# Imported generic specialization loses its native callee owner

Status: OPEN until full compiler/core/tool-server gates qualify this candidate.

The native object defines app.generic_owner.pick_second$i64 / pick_second$str / same$i64 but the former direct-call rewrite could emit bare specialization names. Strict linking therefore fails although the defining module contains the functions. The fix binds the callee to its template's declaration owner, keeps same-module calls local, preserves canonical global/export/entry/extern physical-name handling, and retains the specialization's concrete function signature.

Actual bounded native qualification under producer1fb5 and the matching core-C47 / backfill935 pair passed ordinary imported i64=7, imported text=two and same-module call=42. A concrete external-function control maps23 to28. Source/objects/runtime evidence is attached; no aliases or invented runtime providers are used.

The authored generic-extern case remains unqualified: native code refers to bare foreign_echo whereas direct-HIR monomorphization explicitly names its specialization foreign_echo$i64. That discrepancy is a separate OPEN imported-extern route investigation, not silently changed test expectations. Direct actual-HIR export/global/entry cases and full self-hosted compiler/lib/MCP/LSP/native gates remain UNEXECUTED/incomplete. This PR is a draft; it does not claim full compiler or bootstrap admission.

Duplication review: open broad PRs3196/3191/3123/3066/3182 change transport/signature code but retain mono_requalify(callee,spec_name) in this direct-call block. PR3178 does not change this owner. Their other work is not included.

## Current archive signature conflict resolution

The reviewed current-source candidate retains the archive request design on release_phase3 1aa5db737969205ad97c4db200a061241b6f4d66. MonoTemplateSignatureV1 now records global_linkage from extern/export/global/entry and preserves it through specialization. Physical call naming uses that retained ABI decision plus the defining template owner. The signature digest domain advances to v2 and includes the new bit, invalidating dependent receipts honestly. Both production signature constructors were audited; archive body persistence serializes HirModule, whose codec already carries all four linkage flags. No signature decoder or old raw-layout reader was found in the complete production audit. The broad test-source sweep timed out and is explicitly incomplete.

Exact composed-source qualification is UNEXECUTED. Composition attempts 1 and 2 stopped during source discovery before a cache decision or object build, with malformed multiline else spelling and a reserved pass variable respectively. Earlier imported/local integer/text native PASS applies only to the older qualified producer and source hashes; generic extern, all linkage modes, both body modes, current source, and full compiler/core/MCP/platform gates remain open. The added signature/codec/body-mode tests contain real assertions but have not executed. No all-core PASS or release admission is claimed.
