# Stage 2 hermetic launch strips the supported SCV cold-init opt-in

Status: forwarding and receipt reconstruction fixed; focused contract PASS.
Full Linux/FreeBSD bootstrap remains unverified for this change.

## Observed failure

The admitted pure-Simple parent `c425` was selected for a new full release
checkout at `f1b949825acb4eeb1d3449f45f083b860abcc7c1`. Its compiler-only
entrypoint refused `SCV-E-ADMISSION: compile-event-journal-missing` before any
module compilation. The documented `SIMPLE_SCV_INVENTORY_COLD_INIT=1` remedy
was exported on the second setup attempt, but Stage 2 executes with an explicit
hermetic environment and discarded that export. A full-CLI `check --help`
priming workaround is not supported by this compiler-only parent.

Evidence is retained in
`/home/yoon/dev/simple-linux-phase4-current-release-20261004/build/linux-first-evidence/`
under runs `20261004T074939-1801943` and `20261004T075028-1818462`, with native
diagnostics in `build/bootstrap-linux-current/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`.
Neither attempt compiled modules or deleted the preserved cache.

## Contract

- Default remains absent. Only the exact explicit value `1` is accepted.
- The optional binding follows `SIMPLE_BINARY` identically in the Stage 2
  execution vector and build-args digest.
- The canonical-name helper accepts an explicit optional policy argument;
  its old one-argument result remains byte-for-byte unchanged.
- Stage 3 reconstructs the Stage 2 digest from the recorded binding. Recovery
  validation admits its name only when the recorded value is exactly `1`.
- Stage 2 cache replay restores the recorded policy, clearing any ambient
  export for a legacy transcript. It does not rewrite old admission receipts.
- Duplicate, malformed-length, invalid-value, or malformed-index explicit
  records fail closed. Existing source, producer, runtime, and argument hash
  binding checks remain required.

## Verification

`python3 scripts/check/check-stage2-scv-cold-init.py` passed. It executes the
actual shell fragments used to build the invocation and args digest, capturing
only the compiler execution boundary. Linux and FreeBSD fixtures validate the
real environment-name guard and a child launched through `env -i`, require
opt-in to change the hash, and require Stage 3's actual reconstruction to
produce the identical hash. Cache replay rejects influence from an ambient
invalid export. Five target-platform canonical name vectors retain their
legacy prefix, while invalid caller and recorded values, duplicate rows, and
malformed records are rejected.

These are launcher/admission contract fixtures, not substitute compiler
executions or proof that subsequent SCV admission and bootstrap will complete.
No heavy bootstrap was retried while developing this change.
