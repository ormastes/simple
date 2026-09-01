# SimpleOS primary-tool catalog bundle v1

Status: safe signed-candidate planning increment; no verification run.

Implemented:

- one deterministic required record for the `/bin/simplebox` payload identity;
- eight exact applet aliases without duplicate artifact records;
- rejection of missing, extra, cross-target, alias-drifted, and post-plan
  mutated candidates;
- package-private handoff to the existing cryptographic boot population owner;
- no generated key, fabricated signature, authentication boolean, or claimed
  filesystem-byte verification.

Exact remaining payload gaps:

- no production signed `/bin/simplebox` record, build-policy expected digest,
  or authenticated boot trust-root transfer currently exists;
- no launch transaction hashes the opened `/bin/simplebox` filesystem bytes
  and proves they match the authenticated record before handle promotion;
- no authenticated target payload is available here for x86, ARM32, aarch64,
  riscv32, or riscv64;
- other primary-tool implementations are shell builtins or host-side sources,
  not independently authenticated filesystem payloads, and remain excluded
  until each has a staged binary digest and signed manifest.

Consequently this increment is not a filesystem launch PASS.
