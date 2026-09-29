# Mail POP3 and credential recovery: protocol research

Date: 2026-09-29. Primary sources checked through web search.

- [RFC 1939](https://www.rfc-editor.org/rfc/rfc1939.html): POP3 provides
  maildrop listing/retrieval and deletion. USER/PASS authentication needs the
  original password. UIDL supplies stable identifiers when supported; message
  numbers must not be treated as persistent identifiers across sessions.
- [curl URL syntax](https://curl.se/docs/url-syntax.html): a POP3 URL without
  a message path lists messages; a path identifies a message to retrieve.
- [curl POP3 retrieval example](https://curl.se/libcurl/c/pop3-retr.html):
  demonstrates message retrieval through the existing transport dependency.

Design implications:

- A locally saved one-way password hash cannot replace the server password.
  Use an external encrypted credential manager or avoid saving the password.
  Base64 is not encryption. A local hash is not a password-storage solution
  for remote login.
- Require TLS for new password-authenticated POP3 accounts. Verify certificates.
- POP3 does not provide IMAP folders, flags, or server-side SEARCH semantics.
  Reject unsupported operations explicitly unless a separately specified
  local implementation exists.
- Reading must not delete mail. Destructive deletion needs explicit scope and
  session semantics; do not accidentally delete during retrieval or retry.
- Bound credential retries and distinguish authentication rejection from
  TLS, DNS, timeout, and transport failures. Never replay a potentially accepted
  SMTP submission merely because its final response was lost.
