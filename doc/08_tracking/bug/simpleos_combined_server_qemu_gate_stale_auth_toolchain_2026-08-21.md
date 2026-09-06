# Combined SimpleOS server QEMU gate uses stale authority

Status: open

`scripts/check/check-simpleos-servers-qemu.shs:25` selects the Rust seed and
its SSH probe later uses the hardcoded password `simpleos`. Both contradict the
current production contract: target evidence must use an admitted pure-Simple
compiler, and `src/os/apps/sshd/ssh_session_auth.spl` exposes configured
public-key authentication rather than hardcoded password admission.

Unblock by replacing the build input with a provenance-admitted Simple binary,
injecting an ephemeral authorized public key through the configured credential
owner, removing password/`sshpass` use, and adding live HTTP H1 rejection plus
SSH auth/channel/SFTP transcript checks. Until then this wrapper is diagnostic,
not production protocol PASS evidence.
