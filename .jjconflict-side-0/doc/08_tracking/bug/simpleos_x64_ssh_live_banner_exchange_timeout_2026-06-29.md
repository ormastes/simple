# SimpleOS x64 SSH Live Banner Exchange Timeout

- status: open
- date: 2026-06-29
- lane: SimpleOS hardening / SSH FS exec evidence

## Summary

The x64 live SSH QEMU gate now builds the `ssh_live_entry.spl` guest with the
available release Simple binary, but OpenSSH sessions still time out during
banner exchange before authentication or exec-channel handling.

## Reproduction

```bash
SIMPLE_LIB=src SIMPLE_BIN=release/x86_64-unknown-linux-gnu/simple \
  release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/os/ssh_live_login_in_qemu_spec.spl \
  --mode=interpreter --timeout-ms=900000 --clean --format json
```

## Current Evidence

- Build command uses `release/x86_64-unknown-linux-gnu/simple native-build`.
- Native build succeeds for `build/os/simpleos_ssh_live_32.elf`.
- Guest reaches `[sshd] SSH daemon listening on port 22`.
- OpenSSH transcript files end with `Connection timed out during banner exchange`.
- Serial log repeatedly reports `rt-net version recv branch=nil` followed by
  `disconnect reason=2 desc=no KEXINIT received`.
- The hardening matrix remains `7/9`; `executable_launch_from_fs` and
  `ssh_shell_smf_and_exec` stay failed until authenticated sessions can reach
  `SESSION OK shell ...` transcript output.

## Touched Follow-Up Surface

The host probe now asks for durable session transcripts:

- `build/os/x64-ssh-live.session-smf.txt`
- `build/os/x64-ssh-live.session-exec.txt`

The SSH exec bridge has a focused Simple launch proof path for
`simple.smf --version` and `simple --check`, but live OpenSSH does not reach it
while banner exchange fails.

## Triage note (2026-07-17)

Likely fixed by commits `d5770319715` (2026-07-???) and `7dc03ab537e` (2026-07-???) addressing banner-exchange timeout in SimpleOS x64 SSH. Pending runtime verification: re-run the QEMU gate (`test/03_system/os/ssh_live_login_in_qemu_spec.spl`) to confirm authenticated session reaches `SESSION OK shell ...` output.
