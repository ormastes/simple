# Ownership and handoff

Implementation owner: /root/astra_abstract_text_review. External overlay only; target source is untouched. Shared production scope: both Lean backend entrypoints and one new plugin-owned planning leaf. No MIR/shared schema ownership changes. Sidecars: N/A.

Merge/composition and runtime verification owner: /root. Independent source reviewer: root-designated reviewer after freeze. Requirements remain the selected C2 contracts; this acyclic step does not remove remaining C2 work. Review budget is three bounded cycles. Current packet is cycle-two candidate, CODED_UNRUN_REVIEW_PENDING.

Revision 1 remains immutable. Revision 2 addresses the single independent blocker C2-DECL-01 with a shared admission correction and two real API scenarios. Independent changed-lines review is pending; original runtime and full-C2 gates remain open.

## Current-base port ownership (2026-10-20)

The preceding author/reviewer assignments describe the retained donor work.
Current semantic port owner: `/root/astra_generic_dynload`, isolated
`work/astra-formal-c2-semantic-port-20261020` at release
`30e9aa83e94f557137dbceae22b27973d125d625`. Root coordinates independent Astra
source review and integration; reviewer assignment and receipt are external to
the immutable source packet. No source author self-approval. Sidecars: N/A.
All runtime/proof checks remain UNRUN; authenticated SPipe admission blocks
landing independently of this source work. Maximum three port review/fix cycles.
