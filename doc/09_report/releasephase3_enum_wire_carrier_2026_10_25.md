# Phase3 admission: preserve enum payload carrier

Base: `release_phase3` `3165efd1342804b49dac0c1a28f499aae5171f04`.
Scoped port of release fix `f3ee1b42b1ccd873c067f55ab24b33ca90694368`:
`src/lib/nogc_sync_mut/sffi/enum_wire.spl` is patch-identical to the donor.
`test/04_smoke/enum_wire_boundary_native.spl` retains all donor assertions and
uses the existing `sffi.process.process_exit_i32` facade for failure exit,
avoiding the unrelated broad IO/crypto dependency closure.
No optional typed-bind codec repair or unrelated release change is included.

## Failure and cause

Original admission producer:
`/tmp/phase3-admission-3165/stage2/aarch64-unknown-linux-gnu/simple.rejected`,
SHA-256 `b3ca38774422cfa9bf0b657107326b7cf0bf29b2f4f543830a839b9b45e91942`.
Its retained `stage2-sanity.env.frontend-bootstrap-0.log.stage2-module-path-naming`
reports one worker SIGSEGV (`-139`) after HIR lowering and diagnostic collection
both report zero errors. The aggregate HIR failure is secondary.

An ordinary GDB all-inferior run of that one fixture reproduced the SIGSEGV
inside `hc_enc_hir_expr_kind` at `0x7206b4`, reached through
`hir_module_encode`. No debugger calls, register mutation or fault injection
were used. Disassembly calls `rt_enum_payload`, reads Array length at offset 8
and Array backing at offset 24, then faults dereferencing that backing word.
The old `enum_wire_restore_nil` always allocated a Tuple for a multi-field
payload, even when its typed prototype carried an Array. Hosted Array and
Tuple layouts differ; replacing the carrier makes a native enum match treat
an inline field as an Array backing pointer.

The port validates the prototype as before, preserves its carrier kind, copies
into private storage, and replaces only the requested nil slots. It does not
mutate the original payload or manufacture enum identities. The new first-slot
regression matches the reconstructed Pair while checking its original remains
unchanged. Existing integer, bool, text, tuple and invalid-schema cases remain.

Original artifacts were preserved. Diagnostic reproduction receipts:
`/tmp/module-path-admission-3165-diagnostic/{argv.txt,ordinary-stack-follow.log,ordinary-stack-follow.exit}`.
The first GDB harness attempt stopped on a normally exiting shell child; the
corrected diagnostic continued live inferiors and captured the actual signal.

## Incremental producer and focused evidence

Private output: `/tmp/enum-wire-carrier-rebuild-20261025`.
The retained 190 MB Stage2 cache was copied with reflink support into private
writable storage. The existing bootstrap producer and runtime authority were
reused; source fingerprints were recomputed for the actual changed source.
No bootstrap restart, admission manifest, or release qualification was claimed.

Incremental build: **18 compiled, 1,469 cached, zero failed**; 40.4 seconds
compile + 8.9 seconds link = 49.4 seconds reported total. The builder warns
that its dynload spelling emits a single native artifact; this is recorded as
a provisional bootstrap-produced Stage2 candidate, not self-hosted Stage3.

New candidate SHA-256:
`5fa94dda2a04dccb6a346907b0d7842699bb29d5b585f227d1232109e48f0f1f`.
Runtime authority retains:

- `libsimple_native_all.a`:
  `5f2f65b457a0aa0237726ea25807abc67d7d41859febab6c2b2a69170ca800c9`.
- `libsimple_compiler_backfill.a`:
  `a654803b2c71f383ba4cfd358f22fca1fbb92d1e97dcdad1a3917a8712458b8c`.

The new compiler performs the focused Cranelift compile/run checks below with
that runtime path and unresolved-symbol stub fallback forbidden. Every probe
has its own argv, cache, logs, executable hash and exit receipts.

| Probe | Observed result |
|---|---|
| Original module-path naming fixture | Compile 0, run 0, exact three expected module names, stderr empty. HIR cache store/selfcheck passes; subsequent phases adopt the stored HIR. |
| p2_add | Compile 0, run 0, exact `5` plus newline, stderr empty; HIR cache selfcheck passes. |
| Positional Hello | HIR/MIR/native/link complete; executable run 0 with exact `hello` plus newline and empty stderr. Compile wrapper returns 1 afterwards: `could not restore native-build cache environment`. This remains a separate admission failure, not a compile PASS. |
| Enum boundary with original IO exit import | Compile 1; 49-module closure collects 20 HIR worker failures, first in `lib.common.crypto.secure_memory`; no executable or assertion result. |
| Enum boundary with minimal existing exit facade | Compile 1; 3-module closure lowers `sffi.process` and `sffi.enum_wire` successfully, then the smoke fixture HIR worker crashes (`-139`) after unresolved generic dependency `T` messages. No executable or assertion result. |

The original compiler-to-HIR-cache crash is repaired by this narrow port.
Full admission and Phase3 remain incomplete. The positional cache-environment
restoration failure is delegated separately; no unrelated source workaround
is included here. The ordinary full CLI/SSpec runner and broad compiler/lib/MCP
checks remain unavailable under an admitted producer.
The boundary fixture's hosted-runtime assertion gate remains **BLOCKED**, even
though the original hosted compiler/cache reproducer is now green. The bounded
dependency reduction is retained because it isolates the failing smoke module;
there is no further retry or unrelated generic repair in this change.

## Performance, ownership and checks

The fast path with no nil slots still returns the original prototype without
allocation. Restoring a multi-slot payload still allocates one private carrier
and one enum; copying remains O(arity + replaced slots), with an Array capacity
reservation of the validated arity. No cumulative graph, cache limit or
per-module promotion is added. Source review establishes these bounds;
no standalone performance/RSS acceptance is claimed from compile timings.

Whitespace and working environment guards pass. The SFFI source inventory
fails identically on baseline and port: 411/399 signature variants and
3,687/3,546 migration rows. This preexisting aggregate failure is reported,
not bypassed or called PASS. All new raw declarations have exact unsafe FFI
annotations and remain inside the existing trusted serializer boundary.

Independent source review: GO from the parent coordinator; hosted-carrier
execution and original reproducer are the required focused runtime gates.
