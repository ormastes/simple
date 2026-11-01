# Common traceability layer expert

Source owner: `src/lib/common/traceability`. This is a pure shared contract
layer: typed graph/schema, immutable snapshots, resolution, evidence eligibility,
indexes and bounded projection. App adapters own filesystem/Git/network/report
writes. Compiler adapters provide canonical semantic facts; this layer must not
become a second type checker or process/session lifecycle owner.

Preserve v1 readers and historical provenance; page exhaustion is distinct
from graph completeness and qualification. Full graph export must preserve
cross-page edges. Artifact visibility, compiler publicness and caller
authorization are separate concepts. Public record fields alone cannot certify
producer trust or artifact bytes.

Read [architecture](../../../04_architecture/extreme_typing_traceability.md),
[detail design](../../../05_design/extreme_typing_traceability.md) and
[source-gap audit](../../../01_research/local/extreme_typing_traceability.md).
Proposed interfaces remain unimplemented until reviewed runtime evidence says
otherwise. Source work uses the selected feature/layer knowledge receipt.
