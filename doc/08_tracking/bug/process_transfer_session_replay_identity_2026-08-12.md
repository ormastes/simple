# Process transfer session and replay identity

Status: open

The native transfer allocator packs the low 31 PID bits and a 32-bit local
sequence into a positive `i64` RegionId. This prevents duplicated atomic-counter
collisions for one live same-host parent/child pair, including an exec child.
It does not provide global uniqueness across PID namespaces, PID reuse, stale
frame replay, or process restarts.

The bounded process-frame decoder currently verifies route, destination,
length, and an FNV-1a corruption checksum. Production transport must additionally
bind each request/result to a parent-issued process-session identity and reject
unexpected or replayed `(region_id, generation)` pairs. Authentication for
remote or hostile transports requires the admitted cryptographic wire-hash
contract; FNV-1a is not authentication.

Acceptance evidence:

- production spawn/piped adapter issues a fresh session identity;
- response decode requires the expected session and generation;
- replay of an already accepted frame is rejected;
- PID reuse and namespace simulation cannot authorize a stale frame;
- cancellation revokes outstanding ownership/session tokens;
- tests use an exec-isolated child and bounded timeout/cleanup.
