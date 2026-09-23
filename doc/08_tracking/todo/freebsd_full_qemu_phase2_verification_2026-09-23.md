# TODO: FreeBSD full QEMU Phase-2 verification

Run this only after the Linux bootstrap succeeds. Use the canonical FreeBSD
guest entrypoint:

```sh
sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
```

The completion receipt must prove all of the following from the admitted
FreeBSD Phase-2 binary, without substituting the Rust seed:

- compiler binary check/test execution;
- interpreter binary check/test execution;
- loader binary check/test execution;
- command, exit status, elapsed time, maximum RSS, and retained log path for
  each binary lane;
- no more than 12 build/test jobs or cores;
- the full QEMU bootstrap result and immutable Phase-2 provenance.

Keep this row open until those guest receipts exist. Host-only shell fixtures
verify dispatch isolation but cannot close the FreeBSD execution requirement.
