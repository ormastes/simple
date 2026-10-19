# Warning V2 worker and parent cut

Owner: Astra feature acceptance. Isolated branch `work/managed-warning-v2-20261019`,
base `bb989decd74`. Source candidate only; runtime, native/compiler, SSpec/docgen,
process recovery and performance qualification UNRUN. No full-feature PASS.

Cycle-two correction retains already observed warnings on every later capture
bound or publication failure, not only parser errors. The common failure builder
assigns Warning ordinal zero and Error at the next ordinal. Real-parser bounded
publication and actual obstructed-artifact filesystem regressions are authored;
the publication helper permits only stricter limits than production's 128 MiB.

Depends on the separately owned `managed_parse_compatibility.spl` and
`managed_parse_run_admission.spl` authority packet, qualification producer/evidence
and explicit CLI admission. Their function interfaces were agreed directly with
Astra warning authority. No synthetic direct-owner fixture supplies production
provenance. Existing externally pinned qualification.frontend_identity remains
the provenance route; the worker's local environment check cannot establish it.

Worker V2 installs only when the canonical identity decodes, actual feature and
exact capture-policy settings match it, the cache identity recomputes for the
snapshot worker/target, and all source bytes validate. Action processing repeats
policy checks. V1 rejects dedicated V2 identity and warning mode. The entry selects
V2 only through `--group-root-v2`; V1 `--group-root` remains explicit. Both share
the same bounded mailbox loop, source owner and parser preparation pipeline.

V2 captures the actual reference parser's pre-desugar warning and flat payload.
It restores domains/desugaring, preserves warnings even on failed parses, and
publishes reusable cache receipts only for eligible clean parses. Warning
success retains an artifact but no reusable module receipt/authority. The full
frontend identity, prepared source and cfg decisions bind V2 cache authority.
The filename namespace is `.v2.sdn`/`.v2.authority`; old V1 records are not adapted.

The existing parent scheduler is shared through a small internal typed projection
of separately strict V1/V2 decoders. It retains exact original encoded payload,
action, artifact descriptors, diagnostics and schema-derived reuse eligibility.
This is not a V2-to-V1 wire conversion. Parent admission revalidates that payload
against the ORIGINAL retained dispatch lease/action/snapshot before commit and
uses only the validated projection, including warning diagnostics on success.

`grouped_run_v2` invokes `managed_parse_run_admit_v2` with all independently
expected pins before directory/lock/engine work. V1 rejects V2 environment and
warning policy. No unadmitted V2 entry is exported. Parent protocol helpers import
only common contracts/SDN/diagnostics, never frontend/parser implementations.

Read, publish, admission, journal replay and completed-receipt crash-window paths
use original payload identity. Same-action recovery retains warnings and does not
count a nonreusable result as a cache hit. A different action/lease/source cannot
consume that receipt because contextual decoding rejects it. No cross-action
receipt-reuse route is added. The existing reaped-generation cache copier invokes
the V2 wire-only path, which requires reusable clean results before copying.

Canonical completed diagnostics form an ordered, stable-ID collection under the
exact action receipt; replay does not append a second warning collection. No
exactly-once console delivery promise is made. A new action reparses a warning
module and reports the same semantic warning with its own action scope.

Direct real-parser SSpec covers error/warning/clean/mixed results, replacement
owner clean reuse versus warning reparse, one-file edit, source/policy authority,
explicit entry shutdown and actual parent projection/cache-copy consumers.
The copy test is not proof of live retirement. Remaining required acceptance:
admitted child-process qualifier, actual parent journal/crash-window warning
recovery, cancellation/descendant retirement and allocation/performance evidence.
