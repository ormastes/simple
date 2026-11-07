# Native TCP frame window rejected as non-octet values

Status: OPEN, report only; suggested P1. Not registered in bug_db.sdn.

Producer: tcp-abi-bootstrap/simple.unadmitted, SHA256
507e2849a1624352fd8e1bfd6123cc9df95e7b267b4244f417399449ad10de11.
Pure-Simple compiler, LLVM/core-c-bootstrap, unadmitted; canonical Hello compiled
and executed successfully before this probe. Rust seed used only to bootstrap
that compiler, not to execute this probe.

The full host_authorized_reservation_native_probe builds exit0, runs exit1.
Connect and accept succeed after the TCP address registry candidate. First frame
write fails before a send syscall. GDB resolves the error to TcpStream.write /
tcp_packed_window: "TCP byte value outside octet range".
At entry to TcpStream.write the window has length4/capacity4; its word slots
are [0,0,0x28,0x4c8] (0,0,40,1224). These are consistent with tagged multiples
of8, but exact compiler origin remains unproved. Do not silently mask/truncate
these values or relax octet validation to obtain a passing socket test.

Evidence: build/orchestrator-toolchain-20261107/host-prepare-tcp-v2/
build.log, build.exit, run.log, run.exit, socket.trace, gdb.log,
write-result.log, write-error.log, write-input.log, source.sha256.
The four listed fixture/transport sources match the immutable build snapshot.
No TcpStream library edit or compiler repair applied for this new cause.
Next isolate where frame header u8 values acquire their runtime representation,
then fix the responsible compiler/runtime boundary with a real byte-transfer
regression. The reduced tcp_connect_tagged_text_native_probe remains NOT_RUN.

## Narrowed cause and candidate (supersedes initial slot suspicion)

The header slots [0,0,40,1224] are correct tagged runtime integers, representing
[0,0,5,153]. The array accessor rt_bytes_u8_at normalizes them. Disassembly of
tcp_packed_window shows `sxtb` immediately after that call, so high-bit octets
become negative at `val byte = data[index]; byte as i64`.

Reduced pure-Simple native fixture u8_widen_native_probe.spl:
first build/run exit0/1 reports low127/high153/max255/indexed-103/signed-1.
Second diagnostic variant additionally reports direct153/annotated153. Thus
unsigned parameter widening and direct array widening work; inferred local
copy loses unsignedness. Evidence build/orchestrator-toolchain-20261107/u8-widen/.

Candidate changes only LLVM Copy/Move metadata: after copying source machine
type, also copy source signedness, even if destination had an earlier false
entry. Explicit conversions remain Cast-owned. Previously the `if not has(dest)`
guard retained stale signedness. Source was clean before this lane's edit.
The real transport validation remains unchanged. Candidate compiler bootstrap
and subsequent Hello/reduced/real TCP checks are pending; no fix claim yet.

Candidate rebuilt pure-Simple compiler passed Hello then reduced native probe
(8 assertions): indexed153, direct153, annotated153, signed-1; exit0. Full host
TCP probe started separately; no end-to-end PASS inferred from reduced result.

## Full workflow result: candidate incomplete

host-prepare-tcp-v3 built exit0 and ran exit1 under the copy-unsigned candidate.
GDB again resolves TcpStream.write's error to TCP byte value outside octet range.
The generated tcp_packed_window loop still emits sxtb after rt_bytes_u8_at.
Candidate source and library source match immutable build snapshot. The reduced
straight-line local case is repaired, but the loop case remains broken. Do not
close this bug or describe full signedness preservation as fixed. No send syscall
was observed, so the separately suspected native packed-array ABI mismatch has
NOT been demonstrated by this run.
Next diagnostic must add the loop/range local shape before another compiler change.
For this byte/sign cause: two pre-fix reduced variants, one candidate reduced run,
and one full candidate run consumed four verification cycles. Preserve the six-cycle
cap; bootstrap/Hello outputs are separate prerequisite evidence, not extra fixes.

## Final bounded reduction: branch-and-push shape

Cycle5: inferred and annotated range-loop sums both663, native build/run0/0.
Cycle6: exact range-validation-plus-array-push shape returns Err for valid
[127,128,153,255], native build0/run1. Earlier direct/indexed/annotated/signed
controls and ordinary loop sums still report expected values. This refutes
"any loop loses signedness" and isolates a branch-and-push/live-value shape.
No additional compiler change was made after the partial Copy/Move correction.

Evidence: u8-widen-candidate/build-loop.log, run-loop.log, build-checked.log,
run-checked.log; u8_checked_window_verification_20261107.sdn binds snapshot and
binary. Latest executable fixture contains the failing shape; SSpec regression
also now includes it and is NOT_RUN. The earlier eight-assertion PASS applies
only to the earlier reduced artifact, not this expanded fixture or transport.

SIX-CYCLE CAP REACHED. Stop this cause's build/fix loop; do not reset the count
by renaming the bug, changing workspace, or starting a continuation. Resume needs
an explicit revised repair budget or an independently supplied fix/toolchain.
Compiler candidate remains partial and unqualified. The transport validator has
not been weakened and the full orchestrator goal is not complete.

## Parallel-lane source review and partial preservation (2026-11-07)

This change preserves the previously diagnosed Copy/Move correction and its
regressions on remote release base `4ff1e3b51f54042b919e5a1280f556cda6e79d4a`.
It does not fix or close the checked-window failure. The correction replaces
stale destination signedness with the source signedness, just as Copy/Move
already replaces the destination machine type. Cast continues to own conversions.
Both signed and unsigned sources need this replacement; new direct LLVM owner
specs require sign extension and zero extension respectively for Copy and Move.
These owner specs are authored, not executed.

Provenance is the existing, lane-owned dirty Copy/Move hunk, native fixture,
SSpec and report in `/home/yoon/dev/simple`; no unrelated dirty compiler or
orchestrator files were imported. Retained historical records:

- `.spipe/simple_orchestrator/u8_copy_widening_verification_20261107.sdn`:
  producer `afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`,
  Hello compile/run exit 0, earlier eight-assertion native fixture exit 0,
  full TCP build exit 0/run exit 1. This is not current-source qualification.
- `.spipe/simple_orchestrator/u8_checked_window_verification_20261107.sdn`:
  cycle-six source hash `761c6b811ca0d8d617236652feff7eb885f50d25b2b282069b4e2cb9df833e53`,
  binary hash `691b5732e6dd225c62515374e3e1c30abffc637a3929da0ba41bd46a5522e161`.
  Build exit 0/run exit 1; valid `[127,128,153,255]` rejects with
  `checkedWindowSucceeded=false`. The expanded fixture preserves these exact
  expected octets, signed controls and ordinary-loop sum 663.

Fresh read-only disassembly of that retained `checked` executable confirms
`sxtb x9, w0` at `checked_window+0x4c` (address `0x12624`) immediately after
`rt_bytes_u8_at`; validation and the value later pushed both use this signed
value. No execution or new verification cycle was performed. The recorded
immutable source snapshot directory is no longer present, so no new source
snapshot match is claimed.

Remote release contains `f67fba908a5` (call ABI/GEP), `2d05fc14f01` (unsigned
wrapping arithmetic), and `07321b0fdb3` (MIR Result payload handling). The local
release bookmark was stale; this branch uses the remote base and preserves
those changes. None proves the checked window repaired: its typed byte accessor
calls an i64 runtime return then casts to U8 before local copying. The
cross-block spill pass is unchanged between the old and new release bases;
it reconstructs slot type from the original MIR local and defaults missing
locals to i64. LLVM load width has name-keyed metadata whereas unsignedness
uses ID-keyed metadata. These are inspection targets, not established causes.

The six-cycle cap remains exhausted. No new native build, SSpec run, core/MCP/LSP
smoke, admitted compiler check or TCP execution is claimed for this change.
TCP byte validation, bounds, partial-write/backpressure and EOF behavior are
unchanged. Full transport qualification remains BLOCKED; only the historical
straight-line partial correction and truthful reproductions are preserved.
