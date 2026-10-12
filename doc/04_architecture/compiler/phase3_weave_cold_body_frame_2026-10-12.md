# Complete weave body before cold capture

The retained production sequence is aggregate validation and advice weaving,
then cold typed ABI/SMF/native-witness capture, then optional quiet resolution
and mono. The woven intermediate and the later current mono body need separate
typed descriptors even when the quiet step happens to leave their bytes equal.

`hir_complete_body_frame_v1` shares only the byte grammar for complete HIR and
ordered warning strings, original parent identity and transform boundary pins.
It acquires or promotes no scope. Encoding/decoding require an active borrowed
lease; typed callers still perform original parent and stage checks. It imports
no driver or mono owner and grants no stage admission.

The existing `MonoArchiveCurrentBodyV1` API stays strict
`post-hir-resolved-v1`. Its field order, final newline, key domain and complete
body/warning verification remain unchanged. Shared decoder failures preserve
the original diagnostic categories. The new `DriverColdHirWeaveBodyV1` stays
strict `post-hir-weave-v1` with a separate key domain. Its borrowed reader feeds
the existing complete cold module consumer inside that same active lease.
Decoded modules and frame bytes never become promoted capture results.

Both typed wrappers retain the existing raw owner's 8 MiB total envelope bound,
producer/header/key/checksum framing and secure no-replace/no-follow IO. A large
frame refuses rather than truncates. Full inventory qualification must measure
the actual largest frame; source review does not prove it fits.

The 14-check `weave-cold` native fixture uses real parsed and lowered source,
validates and weaves an actual forwarder, reads the complete woven body, runs
cold ABI plus real immutable semantic files/native witness before the actual
quiet resolver, then stores/reads the resolved body. It compares the old fa04
writer and key bytes on that real resolved HIR, checks ordered escaped warning
bytes and rejects cross-stage keys, changed boundary pins and trailing data.
Fresh post-close read/capture plus inactive/paused refusal cover the lifecycle.
The diagnostic boundary and source inventory rows used in this mechanical
fixture do not manufacture production source/policy or final admission.

The fixture is authored but unrun. The production prerequisite owner must bind
the actual source/policy, ordered gate/weave results, original returned cold
capture and quiet selection before authorizing current mono or final MIR use.
No production archive route or memory improvement is established here.
