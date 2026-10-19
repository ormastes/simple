# Managed parser result V2

Executable: `test/03_system/compiler/incremental/managed_parse_result_v2_spec.spl`.
REQ-IM-007/008/012/016, NFR-IM-004. Runtime/docgen UNRUN.

1. Round-trip typed warning-success through actual canonical SDN module codecs.
   Require artifact readiness independently of reusable=false. V1 rejects V2;
   V2 rejects V1 with no downgrade.
2. Change reuse flags, remove the artifact, or claim ERROR while retaining a
   warning-success payload. Each mutation must reject.
3. Encode/decode an exact snapshot/action aggregate. Warning success has empty
   aggregate error but cannot authorize new-work reuse. A successor lease cannot
   consume the old receipt. A clean reusable result can retain reuse eligibility.

Codec payload fixtures are not parser artifacts or live process evidence.
Actual transport capture has its separate real-parser spec. Parent admission,
authenticated identity binding and live qualification remain separate gates.
