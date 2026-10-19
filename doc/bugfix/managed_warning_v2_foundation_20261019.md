# Managed warning V2: typed diagnostic foundation and pending authority cut

Owner: Astra feature acceptance; branch `work/managed-warning-v2-20261019`;
worktree `/home/yoon/dev/simple-managed-warning-v2-20261019`; base `bb989decd74`.
Root owns execution/integration. Maximum three source repair/review cycles;
this is the first foundation packet. Runtime, docgen and qualification UNRUN.

The exact existing canonical writer is
`std.common.sdn.encode.sdn_encode_canonical`; bounded decoding uses
`std.common.sdn.strict_v1.sdn_parse_strict_v1` and SdnStrictLimitsV1.
The new sibling `managed_parse_diagnostic_v2.spl` uses actual DiagnosticV1,
Severity and admitted ManagedParseModuleV1. It accepts a deliberately bounded
parser profile, rejects unsupported details rather than discarding them, and
recomputes stable IDs from original source digest, logical path, severity, code
and message. No JSON parser or ad hoc SDN serializer is introduced.

Canonical SDN is a fixed 12-element typed profile: version, severity, code,
message, file, absent span, empty labels, identity note array, empty help,
empty children, empty macro trace, absent fix. It is not the existing escaped
line protocol and is not claimed to implement binary events. Individual field
bounds imply a worst-case escaped record under 32 KiB; strict decoding caps
source bytes, nesting and total nodes before constructing DiagnosticV1.

This packet is NOT full warning support. Worker refusal remains unchanged.
ManagedParseQualificationV2.frontend_identity is independently pinned by its
existing admission route, but current snapshot/action carry opaque cache_identity
and no verified capture-policy binding. The separate read-only authority lane
must define the exact producer-to-admission-to-snapshot relation using that
existing attested identity, without inferring digest preimages or introducing
an unauthenticated negotiation record.

Still required: bridge-owned warning transport capture preserving ordinary
cache suppression; additive strict module/action V2 codecs with reusable separate
from reused and aggregate bounds; parent read/cache-copy/publish/admit/replay and
crash-window cut; qualification consumer updates; same-action recovery versus
new-action nonreuse and diagnostic dedup; real warning/error/clean parser and
live process acceptance. Foundation tests cannot close those requirements.
