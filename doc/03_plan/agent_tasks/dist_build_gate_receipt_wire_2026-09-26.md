# Gate receipt wire and CI adapter

Status: codec and adapter source plus focused specs drafted. Astra found no P0/P1 in static review; executable verification remains pending under this session's exhausted self-hosted runner cap. Merge owner: Codex root.

## Wire V1

`encode_gate_receipt_wire_v1(receipt: GateReceipt) -> [u8]` and `parse_gate_receipt_wire_v1(bytes: [u8]) -> Option<GateReceipt>` use the existing provenance-only NBAV length-prefixed UTF-8 frame from `std.nogc_sync_mut.composition.native_build_argv_v1`. This is data, never an executable argv. The frame has at most 65536 bytes and 128 mandatory IDs plus 128 observations. Every item is a fixed-order `key=value` string; the first is `wire=simple-gate-receipt-wire-v1`. Then encode `schema`, `base_revision`, `head_revision`, `candidate_tree`, `protected_policy_digest`, `checker_implementation_digest`, `submodule_closure_digest`, `issuer`, `mandatory_count`, indexed `mandatory.<n>`, `observed_count`, then indexed `observed.<n>.id`, `.status`, `.evidence_digest`, `.reason`. Counts use canonical decimal without leading zeroes. The existing `GateReceipt.schema` must equal `simple-gate-receipt-v1`.

The decoder preflights frame bytes and item/text budgets, checks exact keys and counts, rejects duplicate or unknown fields, extra/truncated items and noncanonical re-encoding, and preserves array order and all admitted text including failure/applicability reasons. NBAV rejects NUL and invalid UTF-8; scalar bounds are 128 bytes for IDs/issuer, 1024 for reasons and 512 for other values. Encoder and decoder reject any value outside these bounds. Neither may change a gate status or synthesize a missing row. `gate_receipt_digest_v1` must be identical before and after a successful round trip.

## CI adapter

`verify_observed_signed_build_ci_wire_candidate_v1` takes independently collected wire bytes plus the same protected caller inputs as `verify_observed_signed_build_ci_candidate_v1`. Decode failure returns `SignedBuildFileDecisionV2(SignedBuildAdmissionV1("FULL_BUILD", ...), "", "")`; success delegates unchanged to that existing controller. Parsed wire is unauthenticated candidate data. Expected identities and mandatory obligations come only from the protected caller, never the submitted receipt.

## Ownership and acceptance

| Lane | Exclusive files | Acceptance |
|---|---|---|
| Codec | `src/app/build/gate_receipt_wire_v1.spl`, focused `test/01_unit/app/build/gate_receipt_wire_v1_spec.spl` | Exact round trip and digest; bounded malformed, duplicate, unknown, trailing and truncated rejection; preserve `FAIL`, `INCOMPLETE`, `NOT_APPLICABLE`. |
| Adapter | `src/app/build/signed_build_ci_wire_adapter_v1.spl`, focused `test/01_unit/app/build/signed_build_ci_wire_adapter_v1_spec.spl` | Invalid wire always selects ordinary build and exposes no artifact path; valid wire delegates to protected checks. |
| Merge owner | This plan, TODO, final review | Keep dirty workflow and hook files with their current owners; do not claim protected collection or live CI admission. |

The future base-owned collector must emit this exact V1 wire from independently observed mandatory gates and prove provenance. The expected gate digest must come from protected observations, never submitted wire. The current specs cover malformed wire, exact round trip including a multiline Unicode reason, and duplicate, missing or failed gate rows selecting the ordinary build. They do not prove successful signature verification, artifact retrieval or `REUSE`. The active self-hosted Simple test-runner verification cap prevents a new runtime PASS in this session. These new files remain untracked in the shared worktree and are not in the earlier 15-file host-handoff bundle.
