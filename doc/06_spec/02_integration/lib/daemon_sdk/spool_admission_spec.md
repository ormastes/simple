# Daemon spool admission regression inventory

Source: `test/02_integration/lib/daemon_sdk/spool_admission_spec.spl`.
Requirements: DAE-01; local transport checks supporting HOST-01.
Status: authored inventory, NOT_RUN. No generated runtime results are available.

| Case | Observable assertion | Result |
| --- | --- | --- |
| Unsafe IDs | Writers refuse before creating either spool directory | NOT_RUN |
| Response identity | A response for another ID is rejected and retained | NOT_RUN |
| Request path binding | A canonical valid file is accepted; changed embedded ID is rejected | NOT_RUN |
| Acknowledgement batch | One invalid ID prevents deletion of every member; a valid batch deletes its file | NOT_RUN |
| Read size limit | Oversized request and response files are refused | NOT_RUN |
| Valid round trip | Directory reads are refused; generated IDs and ordinary fields survive actual file I/O | NOT_RUN |

The tests use private temporary roots and preserve unrelated resources. They
do not establish remote authentication, atomic claim/recovery, directory
ownership or symlink-race qualification. The implementation is applied in
`src/lib/nogc_sync_mut/daemon_sdk/protocol.spl`; it must be verified with the
repository-approved repaired tooling before any pass claim.
