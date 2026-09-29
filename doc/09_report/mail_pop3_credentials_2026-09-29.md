# Mail POP3 and saved credentials: verification

STATUS: WARN / TEST_BLOCKED — not production release admission.

Scope: POP3 read/list and shared SMTP, encrypted credential bridge, bounded
replacement, dev-hub shared JSON configuration/forwarding, home placeholders,
portable launchers, security-hardening TODO. No real user account was accessed.

## Executed evidence

- Existing offline mail library probe: 23 PASS, no FAIL lines.
- New synthetic transport/helper probe: final revision 31 PASS, including
  shared config, replacement and literal home-path expansion. The final run
  followed the Windows-portable stdin change (verification cycle 2).
- Portable attachment regression: PASS with a spaced filename and a base64
  wrapper enforcing stdin-only invocation.
- Actual system curl against a disposable loopback TLS POP3 server: LIST/JSON,
  RETR without mutation, one rejected authentication, and untrusted-certificate
  rejection all passed on the final stdin-based transport revision (4 PASS).
  No synthetic curl or crypto was used for this evidence. Logs remain in
  `build/test-artifacts/mail_pop3_credentials/` (offline_final.txt, loopback_tls.txt).
- Working-tree direct-env-runtime guard: PASS.
- Bash syntax and whitespace checks passed for the inspected revision.
- Independent source review identified and fixed recovery suppression from
  forwarding a stored password command as an explicit override, replacement
  depending on the old secret, boolean positional parsing, hidden login prompts,
  and env-only config directory selection.

Synthetic-helper tests prove orchestration only. They explicitly do not prove
cryptography, native helper build, or cross-host credential-key protection.

## Blocked evidence

The installed executable inspected was
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`.
SHA-256: `44a07ae51c5dd308553cb06203e3e92d0a468b68ffaa28773af0fde0c7ac2c2d`.
Its `--version` reports v1.0.0-beta.14 and explicitly warns that it is a
Rust-built bootstrap seed. It was not used for SSpec, compilation or docgen.

Required remaining evidence:

1. Build/deploy the real `simple-mail-credentials` helper with an admitted
   self-hosted compiler; run `mail_credential_crypto_spec.spl` and its real-helper
   probe. No plaintext fallback or source-at-startup workaround is provided.
2. Execute dev-hub shared JSON/config forwarding and process-prefix SSpec using
   an admitted runtime; verify actual interactive setup and recovery on a TTY.
3. Execute modern SSpec and docgen/sspec-maintain. Authored manuals identify
   themselves as hand-reviewed and unexecuted; no generated PASS is claimed.
4. Complete native helper/runtime validation on Windows/macOS/BSD. Host fixture
   CI on Windows/macOS is narrower and does not certify native Simple crypto.
5. Full suite/lint and branch coverage measurement are not available without
   the approved runtime. No 80% coverage claim is made.

The existing store's unwrapped local key and unauthenticated CBC are explicitly
accepted interim limitations, with a concrete hardening TODO. They are not
described as equivalent to an OS credential vault.

## CI shell dialect repair

The base repository gate parses `.shs` with POSIX `sh -n`; it rejected touched
mail libraries that already used Bash arrays/redirections. Their implementations
now have `.bash` suffixes, with POSIX-parseable compatibility loaders retaining
the public `.shs` paths. The host CI explicitly checks Bash syntax and executes
the real client. The repository gate is unchanged.

Windows CI executed 30 policy checks successfully, then found a native jq path
conversion failure for a literal filename containing shell-looking characters.
Config reads now use stdin redirection, avoiding MSYS argument path heuristics
without evaluating the filename. The targeted config and placeholder groups
passed locally after this change; the Windows rerun is the platform oracle.
This and the shell-dialect loader change comprise the third bounded repair
cycle. Any remaining failure is reported rather than entering another loop.
