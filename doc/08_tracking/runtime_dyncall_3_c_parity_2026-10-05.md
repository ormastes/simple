# C runtime three-argument dynamic call parity

The Simple dynamic-library wrapper already calls `rt_dyncall_3`, exported by
the Rust runtime. The C runtime lacked that symbol. This change adds the same
integer-only three-argument call boundary, its header declaration, and one API
registry row marking the existing Rust/C implementations. Nonpositive function
addresses return -1; arbitrary positive addresses are not validated or made
safe. Admission and callable-address validation remain the loader's job.

The production-linked native selfcheck checks three distinct full-width
arguments (including negative/high-bit values), a negative full-width return,
agreement with `rt_call_ptr_3`, and null/negative function-address rejection.
The owning agent executed the stronger harness successfully and reported
`dyncall_3_host_gate=pass` from:

```sh
sh scripts/check/check-dyncall-3-host.shs /tmp/item5-vector-kernel-abi-dyncall3-strong-20261005
```

The temporary output directory was no longer present during packaging; no
retained binary/output receipt is claimed. The owner confirmed these exact
tested source hashes, which match the relocated files byte-for-byte:

- `src/runtime/test/dyncall_3_host_selfcheck.c`:
  `9a5959b726edafdd89857761a622b544aa83061dd7ddea7f76828dc738487f1e9`
- `scripts/check/check-dyncall-3-host.shs`:
  `bde6c464efc6301d55028934bc434063da392ba43943ef8c4c8f0d4b0ac00c8c`

Packaging on release base `4f55e429c1d76119c5e028a50819267147482022`
preserves the tested nine-line implementation, declaration, harness and runner.
Shell syntax and diff checks passed; the green native criterion was not rerun.
One existing `repo-hygiene.yml` run_guard invocation wires the check alongside
the hosted native runtime checks; it does not change job policy. The runner
requires a POSIX Clang/GNU-linker-compatible host, pthread and libdl; Windows
and macOS execution are not established by this evidence.

No Simple vector wire/session changes are included. This establishes only the
C call-boundary parity, not dynamic provider admission, AVX512 execution,
Phase2 application correctness, or performance. Canonical landing gates remain
the landing owner's responsibility.
