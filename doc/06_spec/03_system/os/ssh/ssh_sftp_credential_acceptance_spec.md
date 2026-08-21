# SSH/SFTP credential acceptance

This executable acceptance scenario proves the in-process security boundary;
it does not claim a live network or external-client cryptographic exchange.

- A configured Ed25519 identity must pass RFC 4252 signature verification
  before its principal can request SFTP.
- SFTP admission fails before authentication, for an empty principal, and for
  empty or over-capacity channel ownership.
- A tampered signature never reaches SFTP admission.
- An admitted protocol session negotiates SFTP v3 while filesystem operations
  remain fail-closed behind the separate VFS capability boundary.

Executable source:
`test/03_system/os/ssh/ssh_sftp_credential_acceptance_spec.spl`.
