# Host primary attachment consumed-record contract

Source: `test/03_system/app/orchestrator/feature/host_primary_attach_record_v1_spec.spl`

Requirements: ORCH-02, HOST-02. Status: NOT_RUN, manually maintained source
companion. SPipe generation and maintenance scoring were not executed.

| Scenario | Intended observable result |
|---|---|
| Roundtrip stdin and tty plans | Exact canonical record and all nested plan/evidence fields survive encoding and decoding. |
| Alter operation or expiry | Another helper operation and nonpositive deadlines are refused. |
| Alter retained hashes | Every malformed operation, packet, execution-proof, or receipt digest is refused. |
| Alter nested launch | Changed argv, stale plan digest, duplicate fields, and noncanonical plan bytes are refused. |
| Substitute output archive | Valid output-follow records and plans cannot decode as primary records. |
| Alter outer schema | Unknown, duplicate, missing, mistyped, and noncanonical fields are refused. |
| Replay consumption | Exclusive publication refuses identical and changed valid records while preserving original bytes. |
| Leave partial consumption | An existing partial record blocks publication and remains byte-for-byte unchanged. |

Filesystem scenarios use unique temporary directories and remove their own
fixtures. They test the real shared publication primitive used before Host
primary opening. They do not construct native owners or bypass admission.

This companion makes no native attachment, input/geometry, cleanup, settlement,
Windows, coverage, or production-readiness claim. The source-only Host owner
and remaining integration are described in
`doc/05_design/host_primary_attach_owner_v1.md`.
