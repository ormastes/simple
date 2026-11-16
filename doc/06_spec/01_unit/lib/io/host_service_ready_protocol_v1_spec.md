# V6-only setup/ready protocol source cases

Status: **NOT_RUN**. Nine source-authored production-helper cases in
`test/01_unit/lib/io/host_service_ready_protocol_v1_spec.spl`.

1. Native GLOBAL and Unicode parent path spelling survives exact final split.
2. Invalid/reserved/oversized derived leaves refuse before root or entropy.
3. Exact canonical private setup8 bytes, final LF and public SHA pin correlate.
4. Legacy two-field data, altered generator/size and noncanonical bytes refuse
   even when the supplied digest hashes that malformed input.
5. Public ready9 contains no secret field and returns metadata only.
6. Cross-setup pin/UID associations refuse.
7. Only exact positive bounded127.0.0.1 port syntax is admitted; this is not
   liveness or listener authentication.

8. Exact three-line parent.lease with final LF and expected Host authority
   decodes to its precise SHA; malformed header/case/lines/authority refuse.
9. Different exact leases select distinct immutable existing-journal keys;
   traversal or a ready record for another lease is rejected. Snapshot
   equality is DATA only and does not establish Host liveness.

Known test keys/UIDs are caller data for pure codec testing. These cases do not
prove OS entropy, actual private file access, publication or native MAC custody.
