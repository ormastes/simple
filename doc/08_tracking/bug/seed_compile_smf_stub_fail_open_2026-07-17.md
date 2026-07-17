# `simple compile <x.spl> -o <x.smf>` emits a 219-byte stub and exits 0 (fail-open)

**Date:** 2026-07-17
**Severity:** high (fail-open: silent no-op artifacts look like successful builds)
**Status:** partially fixed — pure-Simple dynSMF detection landed 2026-07-17
(export-witness check in `src/os/smf/smf_dynlib.spl` /
`src/os/smf/dynsmf_session.spl`: artifact status now scans the artifact's own
bytes for each required `exports` name as a null-terminated ASCII run — the
real SMF string-table convention — and unconditionally requires the payload
to exceed the known 219-byte stub size (a bare name match alone is not
sufficient, since the stub already contains a literal `main` symbol),
failing closed with reason `stub_artifact` otherwise; verified via
`--dynsmf-status` on all 7 real `build/dynsmf/*.smf` artifacts on this host).
The root Rust emitter fix (making `compile -o *.smf` either emit a real
payload or fail closed) is still open.

## Symptom

On the current seeds (`src/compiler_rust/target/{release,bootstrap}/simple`,
2026-07-17):

```
$ simple compile hello.spl -o hello.smf   # hello.spl = print("run-ok")
$ echo $?          # 0
$ ls -l hello.smf  # 219 bytes
$ simple run hello.smf ; echo $?
# no output at all, exit 0
```

The emitted SMF is a valid-magic (`SMF\0`) container with a tiny `code`
section and a `main` symbol, but it executes nothing. Every input produces
the same 219-byte stub — all seven `build/dynsmf/*.smf` artifacts on this
host are byte-identical stubs of exactly this size.

## Why it matters

- Double greenwash: `compile` succeeds without producing a real module, and
  `run <stub.smf>` succeeds while executing nothing.
- The dynSMF lane's `SMF\0`-magic validation passes on these stubs, so
  "precompiled module ready" evidence can be hollow. The 2026-07-17 sidecar
  hardening (abi/srchash/ifacehash) binds staleness and ABI but cannot detect
  a stub payload.

## Expected

Either `compile` emits a real executable SMF payload, or it must fail closed
(nonzero exit + diagnostic) when the backend cannot emit one (e.g.
interpreter-mode seed without the SMF backend). `run <smf>` executing zero
user code should not exit 0 silently.

## Fix direction

- Determine whether the seed's `compile -o *.smf` path is intentionally
  stubbed (bootstrap-only seed) — if so it must return nonzero + a clear
  "SMF emission unsupported in this binary" error instead of a stub.
- Add a payload-honesty check to the dynSMF artifact status (e.g. minimum
  code-section size or a compile-receipt sidecar) so stub artifacts classify
  as invalid, not ready.
- Add a deliberate-red contract: compile a print-program to SMF, run it, and
  require the expected stdout (absolute oracle), not just exit 0.

## How found

Tooling-surface smoke matrix during the 2026-07-17 test-runner hardening
campaign (`hello.smf` stub matched the seven dynSMF stub artifacts).
