# Trust-root stage2 bootstrap SIGILLs (rc=132) in candidate frontend smoke under cranelift

Date: 2026-09-25
Host: aarch64 Linux, 20-core, 121 GB RAM. `/proc/cpuinfo` exposes no model
name; flags include `sve sve2 sveaes svebitperm i8mm bf16 sha512 atomics`
(Neoverse-N2-class feature set).
Tree: `work/release/rc1` at 7289de16fab (main 85a669f5b21 + 1.0.0-rc.1 bump).

## Repro

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 --mode=dynload --jobs=8 --backend=cranelift
```

(`--backend=cranelift` is policy-sanctioned — `llvm-cranelift:cranelift` is
accepted at bootstrap-from-scratch.sh:667 — and required on this host because
LLVM 23.1.1 is not installed; the documented rootless tree
`/mnt/data/toolchains/llvm-23-root` is not mounted here. `--mode=dynload` is
mandatory for `--stop-after-stage2`, line 482, so no mode variation exists.)

## Failure

Stage 1 (Rust seed + native-all + runtime-nolto) builds clean. Stage 2 starts,
then the sanity gate fails:

```
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=132)
error: Stage 2 bootstrap compiler sanity failed
VERDICT — ABORTED: stage=stage2 exit=1
```

rc=132 = 128+4 = SIGILL. Logs:
- `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`
- `.simple/storage/build/bootstrap/logs/aarch64-unknown-linux-gnu/stage2-native-build.log.refusal`

The smoke parses `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`
(source closure + load_sources succeed; the SIGILL hits during/after parse
when the freshly built stage2 candidate does the positional build).

The wrapper cross-references
`doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md`, but the
signature here is an illegal instruction, not empty MIR bodies.

## Notes for investigation

- The Sep-21..23 stage2-admitted/stage3 binaries under
  `/home/yoon/dev/simple-boot0921/build/bootstrap-0921/` run fine on this same
  host (`--help` works), so whatever backend/codegen produced THOSE binaries
  was host-compatible. Determine which backend built them; if it was the LLVM
  backend, this may be a cranelift-only aarch64 codegen defect (e.g. target
  feature selection emitting beyond-baseline instructions, or a dynload-stub
  trampoline bug).
- `bootstrap-from-scratch.sh:1912-1916` already forces cranelift for some
  seed-side frontend smokes, so a cranelift aarch64 smoke path is exercised in
  CI (x86_64 runners) but apparently not on aarch64 hosts in CI.
- Retrying with identical flags reproduces the same smoke failure shape (the
  trust-root lane allows no flag variation: backend fixed by host toolchain,
  mode fixed by --stop-after-stage2).

## Impact

Blocks the local trust-root stage2 bootstrap (and therefore local
`simple release version-check`) on this aarch64 host. CI lanes (x86_64
runners) are unaffected; the 1.0.0-rc.1 release validation proceeds via CI.
