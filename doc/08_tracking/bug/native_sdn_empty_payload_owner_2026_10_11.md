# Empty SDN enum containers lose payload type

Status: OPEN. Canonical bug ID: `native_sdn_empty_payload_owner_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/2982

Original failure: C35 runner MIR rejects SdnValue.Dict and Array payload0 type mismatches for untyped empty literals.

Workaround commits:

- `7324234fe33dcc7292849f4907439353228d8535`; recovery parent `ea9224a83a64cd20e21d013cf1c2652f891999c4` (review only).

Current qualification: Standalone C35 ARM native fixture PASS, preserving tags/nesting. No RISC-V execution or full-runner qualification claimed.

Producer: `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-runner-enum-workarounds-20261011/build/native_probe/c35-workaround-qualification/sdn_empty_container_workaround/arm-attempt2/result.json`.

Reproducing/prevention source: `test/fixtures/compiler/sdn_empty_container_workaround/main.spl`.

Background fix owner and removal condition: Enum-constructor inference/MIR payload owner. Remove typed empty locals only when original empty constructors pass HIR/MIR/native object and runtime nested-container controls.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: 7324234fe33dcc7292849f4907439353228d8535 -> c3f188f781aa0853baec2fd87ebdcf7f45d0d9cf (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: ARM fixture source 3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a contains preceding SDN workaround7324234fe33dcc7292849f4907439353228d8535; do not treat runner as qualified.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.

Additional actual-consumer source workaround: Additional temporary SDN parser payload workaround https://github.com/ormastes/simple/commit/b09df8623d9d70731e33ea3678a91692fe7f95f6 (four canonical source markers): typed tuple-projected array aliases and typed block/inline dictionary accumulators. Frozen integration a9b5343d9dfbb9e6a38e074d7162092c58191b34; original branch SHA is not a release landing claim.

Actual C36 env_access_host closure HIR/MIR PASS and 59 of74 native objects retained; aggregate FAIL on15 declaration-only dependencies. Changed lib.common.sdn.parser object ELF64 ET_REL EM183,99584bytes SHA25663c21ea6f26d31db33483c69b0b603d4e4eff8eceaa859f03fc4dd69a82bc641;39 module-owned symbols. Producer 5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235; source a9b5343d9dfbb9e6a38e074d7162092c58191b34; source SHA2568f92aacf23303d19e8ce525fe3f06004301f7d3271d3712b5c56d796267e3e3c. Evidence /home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-sdn-frontend/consumer-env-access-host/retained-object-inventory.json. Capsule has missing-witness-facts: diagnostic object emission only, not cache/admission or runtime qualification. New parser fixture and RISC-V remain unrun; prior732 narrow ARM runtime proof is separate.

Removal additionally requires original tuple payload/dictionary forms and parser payload fixture controls on the repaired producer; keep OPEN.
