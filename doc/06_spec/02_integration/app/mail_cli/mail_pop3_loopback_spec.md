# POP3 over loopback TLS with actual curl

Executable: `test/02_integration/app/mail_cli/mail_pop3_loopback_spec.spl`.
Fixture: `test/01_unit/tools/mail_cli/fixtures/loopback_pop3_probe.py`.
Requirements: REQ-001, REQ-003, REQ-006.

Evidence class: **local protocol interoperability**. This executes the production
Bash mail client and actual `/usr/bin/curl`, with a Python stdlib TLS POP3 server
listening only on `127.0.0.1`. All accounts, passwords, keys, certificates, and
configuration files are disposable synthetic fixtures. No encrypted helper is
substituted or claimed to pass crypto acceptance.

1. Generate a disposable self-signed certificate with loopback IP SAN.
2. Configure curl to trust that certificate, then list and retrieve a message.
3. Assert JSON identity/subject, body bytes, and no DELE or STORE requests.
4. Supply an incorrect password and assert one authentication attempt, exit 67,
   and actionable recovery guidance.
5. Restore system certificate trust and assert certificate failure exit 60.
6. Stop the server and remove the temporary configuration and certificates.

## Executed evidence — 2026-09-29

The Python fixture passed on the final revision after curl config input changed
from a descriptor path to stdin for native Windows compatibility. This was the
second verification cycle, required by that transport implementation change.
Retained log:
`build/test-artifacts/mail_pop3_credentials/loopback_tls.txt`.

```text
actual_curl_tls_pop3_list: PASS
actual_curl_tls_pop3_retrieve_without_mutation: PASS
actual_curl_authentication_rejected_once: PASS
actual_curl_untrusted_certificate_rejected: PASS
```

The test requires Linux's `/etc/ssl/certs/ca-certificates.crt` for its negative
certificate case. This run is Linux evidence, not macOS/BSD/Windows evidence.
It does not establish real-provider compatibility, STARTTLS interoperability,
SMTP delivery, native Simple execution, or encrypted storage correctness.

Native SSpec execution and `spipe-docgen`: **BLOCKED / NOT RUN** because no
admitted self-hosted Simple runtime is available. This manual is hand-reviewed;
only the Python interoperability fixture's execution is recorded as PASS.

<details>
<summary>Executable specification</summary>

The modern SSpec invokes the isolated protocol fixture and asserts exit status
plus all four concrete protocol check results.

</details>
