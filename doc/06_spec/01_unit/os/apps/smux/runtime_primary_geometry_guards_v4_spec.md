# smux primary Geometry V4 pure guards

Source: `test/01_unit/os/apps/smux/runtime_primary_geometry_guards_v4_spec.spl`.
Status: **NOT_RUN**. Seven source-only scenarios; manually authored companion.

The production-helper assertions cover current Geometry lease expiry, right,
principal, nonce, target, attempt and dimension/area bounds; complete request
equality including both targets and retained lease metadata; finite incremental
deadlines and overflow refusal; every UID/GID/PID/socket-device/socket-inode
peer field; prewrite Rejected versus attempted Unknown and acknowledgement
preservation; exact unresolved replay versus changed/old/new/rotated attempts;
and real bounded-issuer revoke/expiry plus Geometry rotation denial while an
independent Input right can still be issued and checked.

The record fixtures contain no native exchange. Current issuer retirement
preserves Unknown metadata; lease expiry or rotation supplies no no-delivery
proof. Input and Geometry metadata remain separate. Codec companion coverage
also retains legacy resize attempt zero decoding and positive explicit resize
attempts, with offset/maxBytes fixed to zero.

**NOT_COVERED:** native owner construction, live adoption, actual socket peer
observation, full- or partial-resize sends, applied geometry, HTTP effect
acknowledgements, retained cleanup carriers, cancellation/close behavior,
canonical pane publication, and end-to-end handler continuation. Peer metadata
comparison is not a process-incarnation credential. No live session or native
cleanup success is fabricated. Tests/build/runtime checks were not executed.
