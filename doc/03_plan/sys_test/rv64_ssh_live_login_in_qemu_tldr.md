# RV64 SSH Live Login in QEMU TLDR

## Purpose

Keep the RV64 SSH QEMU lane honest: static source contract plus opt-in live OpenSSH proof.

## Required Evidence

- Static SSpec passes `6/6`.
- `rv64-ssh` build works even when the test runner uses `SIMPLE_BIN=bin/simple`; the child native-build must select `src/compiler_rust/target/bootstrap/simple`.
- Live run with `SIMPLEOS_RV64_SSH_LIVE=1` prints `TEST PASSED`.
- Docgen reports `0 stubs`.

## Flow

```text
SSpec static contract -> RV64 image build -> QEMU boot -> OpenSSH auth/exec -> bad-auth fail-closed
```

## Open

Fresh live QEMU proof is still required for channel-open confirmation, return-to-accept, `simple`, `simple.smf`, and bad-auth.
