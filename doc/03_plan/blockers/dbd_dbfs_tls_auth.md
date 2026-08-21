# dbd production-readiness blockers

DBD now owns bounded authenticated TLS record framing, mutable-byte RESP AUTH,
post-auth command framing, response/session budgets, and retryable socket-close
quarantine. `DbdDbfsAdapter` also identifies a mounted `DbFsDriver` and permits
only bounded recovery reads whose source can be verified.

Production advertisement remains fail-closed for three concrete reasons:

- boot has no mutable credential provisioner that proves caller-side secret
  zeroization;
- boot has no admitted certificate/private-key/entropy owner for the existing
  TLS handshake boundary;
- `DbFsDriver.fsync`/`fdatasync` is unsupported, so DBD cannot acknowledge a
  crash-durable mutation or safely promote its diagnostic adapter.

Filesystem launch is separately bounded by
`dbd_admit_filesystem_launch_v1`: only `/sys/services/dbd`, a verified
executable format, a bounded non-empty image, and a canonical SHA-256 receipt
reach readiness evaluation. Arguments are forbidden so credentials cannot be
placed in process metadata. A valid image still returns the stable production
owner blocker; filesystem presence is never treated as security readiness.

These properties remain explicit in `DBD_CAPABILITY_STATE` until the owning
boot and DBFS contracts provide falsifiable evidence. No caller-controlled
readiness boolean can promote them.
