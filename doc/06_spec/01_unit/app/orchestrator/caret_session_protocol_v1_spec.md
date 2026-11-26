# Caret local listener authority

Source `test/01_unit/app/orchestrator/caret_session_protocol_v1_spec.spl`.
Status `AUTHORED_NOT_RUN`.

- Bind the actual IPv4 loopback listener and read its assigned port through
  the Caret runtime metadata loader. Preserve the selected server and context
  labels, and close the listener.
- Use the normal Caret client with each invalid runtime-file destination.
  Refuse remote DNS, remote IPv4, other loopback spellings, and noncanonical
  ports before opening a socket or sending the local bearer.

The configured remote SSH route has its own protected gateway profile.
