# Mail credential NFRs

Selected profile: existing Simple encryption with documented security debt.
No additional cryptographic algorithm is introduced by mail-cli.

- Keep secrets off external-process argv and diagnostic output.
- Secret config writes use private temporary files and atomic replacement.
- New POP3 accounts require implicit TLS or mandatory STLS with certificate checks.
- One authentication replacement attempt per operation; no transport-error prompt.
- Noninteractive operation never consumes body stdin for a password prompt.
- Inbox limit bounds message retrieval; preserve original protocol exit errors.
- Offline fixtures assert protocol selection, auth retries, password precedence,
  persistence failures, unsupported operations and IMAP/SMTP regressions.
- Compiled credential-helper acceptance and dev-hub tests require an admitted
  self-hosted runtime. Host-native cross-platform verification remains explicit.
