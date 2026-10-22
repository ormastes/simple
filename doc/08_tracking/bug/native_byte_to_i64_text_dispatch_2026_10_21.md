# Native byte-to-i64 text dispatch, 2026-10-21

Status: permanent compiler fix SOURCE GO; execution on rebuilt producer pending. Canonical bug-index reconciliation pending a qualified full CLI; no seed/check-dbs fallback was used.

Retained pure producer SHA256: 645e62a815d076d77a61b01daa6e86c1330632686c18ce4c56cccd860a4a714a. Its SDN separator function routes indexed u8.to_i64 through text conversion, established by retained disassembly in the native-byte-to-i64 repair causal packet. Actual public representation caller returned11; further bounded diagnostics showed missing mapping keys.

Permanent compiler repair commit: fde0c65236abd91faae2e07c17800379bcbb67bd. Narrow integer MIR values now retain numeric authority; erased I64/Any remains unproven. Reviewed native regression fixture is committed in b0a0cd289e1f600d70ebfae890a275cf9dae6ab9. Neither source review nor compiling the producer source is runtime qualification of the repair.

Temporary SDN compatibility workaround commit: acb6792b859fb33cbdcde9d62fdc373cef991e73. Exact parser source SHA256 b5364ec2101522d381a50307ad42c09493d74de3ebd8cd2717ae30534a59fcd1, reviewed patch ae104e0005118e569b18a9f5e6840da2e55eebf5698d98946e031d5bf6896b20. Only six local text.bytes indexed receivers change to explicit i64 casts. Grammar, errors, offsets, defaults and APIs are unchanged. Each site carries the bug tag.

Actual old-producer compatibility evidence: generation-7-cast-compatibility-path-corrected/unit-0/execution.json under the external Phase3 campaign records exit0 and the required marker for 58/61, indexed128/255, u8 parameter255 and signed i8-1; executable SHA256 5e3a2ff6f73dd3d1a1d5c43ddecc6a951b801871bac2592e12f367ec47dec0bc. Changed-parser acceptance is pending at this record's creation; retain original caller expectations and require UTF8 block/inline controls.

Recovery: after the rebuilt repaired producer passes method aliases, all256 octets, signed/unsigned and text/float controls plus unchanged SDN public-consumer acceptance, remove only these six workaround substitutions/comments. Retain the compiler fix and regression fixtures. Background cause/repair owner: native-byte-to-i64 repair lane, independent Astra review. No current runtime PASS or full Phase3 PASS is asserted.
