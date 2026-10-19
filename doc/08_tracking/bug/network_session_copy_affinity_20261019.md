# Network sessions: runtime alias and affine lifetime qualification

Status: OPEN, execution UNRUN. This is not an established use-after-close fix.

Only owning connect/accept/bind factories create text sessions; no caller-owned raw transport is adopted. Ordinary class references are intended to share the decoder and close state. Two actual loopback scenarios now close through a second session reference and require refusal/idempotence through the first. Until executed on each admitted engine, this is an authored oracle, not a reference-semantics guarantee.

Resource/Isolated integration, independent clone safety, descriptor-number reuse, container escape, returned Result transport, concurrent use and drop behavior still need authoritative lifetime evidence. Do not treat private fields or unsafe metadata as affine enforcement. Existing resource_use_after_move_spec.spl is the relevant compiler mechanism; this source port does not change it or add a global registry.

The previous raw-adoption API removal and five production parser/HIR surface cases are retained. No session API permits reopening/resetting a closed session. Full file/network lifetime acceptance remains separate from source-reviewed unverified landing.
