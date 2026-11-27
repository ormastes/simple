# Smux remote cleanup completion replies

Status: **AUTHORED_UNRUN**. Source:
`test/01_unit/os/apps/smux/remote_cleanup_reply_spec.spl`.

REQ-SMUX-LOCAL-004: a kill request whose actual owner returns `Ok(false)` must
report cleanup pending and yield a nonzero CLI result. Only `Ok(true)` reports
session/window removal. Errors preserve their explicit failure message.

Three pure scenarios exercise the same result renderer used by production
dispatch and the actual hosted-client reply classifier. They cover pending,
completed and failed session/window outcomes. No supplied boolean is treated
as native cleanup or host settlement evidence. Actual signed binding and
cleanup/ACK execution remain separate system qualification requirements.
