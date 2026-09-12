# macOS seed build fails: 11 `rt_process_*` symbols are defined in BOTH the Rust and C runtimes (2026-09-13)

Status: **OPEN — blocks every macOS bootstrap lane, including Stage 2 verification.**
Not a regression of any `.spl` change; it is in the Rust seed + C runtime.

## Verdict, verbatim

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap \
   --mode=dynload --jobs=half
...
Building Rust seed compiler + runtime library...
error: rust-seed-build failed with exit 101
```

`logs/aarch64-apple-darwin/rust-seed-build.log`:

```
error: linking with `cc` failed: exit status: 1
  = note: duplicate symbol '_rt_process_owned_v3_observation_value' in:
              .../deps/simple_runtime.simple_runtime.<hash>-cgu.11.rcgu.o
              .../out/libruntime_sffi_c.a[24](<hash>-runtime_process_owned.o)
          [11 more]
error: could not compile `simple-runtime` (lib) due to 1 previous error
```

12 `duplicate symbol` lines, 11 distinct symbols:
`rt_process_owned_v3_observation_value`, `rt_process_owned_v3_capabilities_value`,
`rt_process_observation_v4_{collect,cancel,close_cwd,cwd_digest,start,poll,pin_cwd,ack_collect,capabilities}_value`.

## Cause

`src/compiler_rust/runtime/src/process_observation_v4_twins.rs` (landed in
`920b7c2dcb3`, "L7/L8 host-ABI lane 1/2 — Codex V4 port packets") defines each of these
as `pub unsafe extern "C" fn`, and its own doc comment says so explicitly:

```
/// Contract: C twin `rt_process_owned_v3_observation_value` at ...
pub unsafe extern "C" fn rt_process_owned_v3_observation_value(...)
```

The C twin is real and still present — `src/runtime/runtime_process_owned.c:2051` (and a
second definition at `:4470`). A "twin" that keeps the SAME exported symbol name is not a
twin at link time, it is a redefinition.

Why macOS and not Linux: the C runtime archive is linked with
`-Wl,-force_load .../libruntime_sffi_c.a`, so every member object is pulled in
unconditionally and Mach-O `ld` rejects the duplicate outright. ELF linkage on the Linux
lane does not surface it the same way, which is how this landed green.

## Impact

Every macOS bootstrap stops at the FIRST step (seed build) and reaches no stage at all.
The macOS Stage 2 blocker tracked in
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md` therefore cannot be
re-verified on this host until this is fixed — the link-nil fix in that record is
committed but unverified end to end for exactly this reason.

## What a fix must not do

Deleting either side blindly collides with the `rt_*` dual-implementation directive and
the `push-rt-dual-implementation` ratchet. The twin pair is intentional; what is wrong is
that both halves export the same C symbol. Options, in the order they look cheapest:

1. give the Rust twin a distinct exported name (`#[export_name = "rt_..._rs"]`) and select
   between the two at one call site, which is what a twin is for;
2. compile the Rust twin only when the C one is excluded (a cargo feature the macOS lane
   does not enable);
3. drop the C member from `-force_load` for these objects — fragile, since force_load is
   what guarantees the rest of the runtime is present.

Also worth checking while there: `runtime_process_owned.c` defines
`rt_process_owned_v3_observation_value` at two separate lines (2051 and 4470). If those
are not mutually exclusive under `#ifdef`, that is a second defect in the same file.

## Reproduction

Any macOS host, from a worktree with a virgin evidence root:

```
chmod -R u+w .simple/storage/build/bootstrap && rm -rf .simple/storage/build/bootstrap
sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap \
   --mode=dynload --jobs=half
```

Fails in ~4 minutes, well before any Simple compilation.

## Scope and mechanism — what is verified and what is not (added before landing)

Verified:
- `git diff origin/main..HEAD -- src/compiler_rust src/runtime` is EMPTY for the branch
  that hit this, so no change on that branch can be the cause.
- Both halves landed in the SAME commit, `920b7c2dcb3` (Sat Sep 12 20:02 +0900):
  `process_observation_v4_twins.rs` and `runtime_process_owned.c`.
- Run 10's worktree (`agent-a87b4c8362f754818`) has NO `rust-seed-build.log` at all —
  it never built the seed, it reused a warm authority. So there is no evidence any
  macOS seed has linked successfully since `920b7c2dcb3`, and equally none that it was
  ever green after it.

NOT verified, stated as such:
- The ELF/Mach-O asymmetry. The plausible mechanism is that `-Wl,-force_load` is
  Mach-O-only, so on Linux the C archive member is lazily loaded and never pulled in
  once the Rust symbol satisfies the reference — ELF `ld` also rejects duplicate strong
  symbols, so "ELF is more tolerant" would be wrong. NOT checked on a Linux host; do not
  repeat it as fact. The "Why macOS and not Linux" paragraph above is a hypothesis.
- Whether `origin/main` is red for every macOS host or only from a virgin evidence root.
  Any lane with a warm `rust-authority-*` target (like run 10) skips the relink entirely
  and will not see this.
