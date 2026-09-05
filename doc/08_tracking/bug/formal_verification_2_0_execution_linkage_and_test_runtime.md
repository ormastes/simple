# Formal Verification 2.0 execution-linkage and validation blockers

Status: open
Owner: Formal Verification 2.0 integration lane
Updated: 2026-08-12

## Remaining contract blocker

The pure frontend now retains typed `in:`/`out:`/`out_err:`/invariant/decreases
clauses through HIR and MIR. Canonical V2 obligation generation derives input,
state, transition, frame, recursion, and order authorities from serialized MIR;
the Lean backend ties pure and admitted typed-global pre/postconditions to the
actual generated function/state-transformer call. Exact Result normal/error
routing, pure invariants, termination, and global frame theorems are present.

Effectful invariant state binding now reuses existing zero-argument ghost-call
syntax without adding proof grammar. The retained HIR SymbolId and name must
resolve to one exact Boolean MIR function with closed read-only typed-global
effects; generated initialization/preservation theorems apply that function to
the actual pre/post state. Name-only matches, writes, and argument-only
lookalikes are rejected.

Module-level owner obligations now bind the predicate function body and region
manifest through `StatePredicateBindingV1`. Typed receipts require exact
namespace-qualified initialization/preservation roots plus artifact, cache,
axiom-audit, trust-manifest, and independent-replay identities before
`source_refined`. Actual independent replay remains blocked by an unprovisioned
pinned `lean4export`/`nanoda` adapter. Heap/capability regions and general effectful CFG
lowering remain unsupported rather than guessed.

## Self-hosted validation blocker

Every discovered `bin/release/<triple>/simple` candidate identifies itself as a
Rust bootstrap seed. Repository policy prohibits treating that seed as the
default compiler/test runtime, so the new Simple unit and SPipe tests currently
have static diff evidence only. Diagnostic-only focused checks also take more
than 120 seconds and time out without a source diagnostic; the shell pipeline
currently masks that timeout with exit status zero.
One bounded direct diagnostic of the new replay runner also exited 124 after
35 seconds without a source diagnostic. It was not repeated.

Unblock condition: deploy a genuine pure-Simple self-hosted binary at the
canonical release path; make the focused checker finish within 30 seconds warm
and propagate timeout/failure as nonzero; then run each focused acceptance
check once, followed by the required compiler/lib/MCP/LSP and environment
audits. Do not convert a seed result into release evidence.

Lean 4.33/Lake 5.0 are available and a direct `mir_dce_tv` replay produced
real transitive axiom output (`propext` or no axioms per root). Lean 4.33 also
ships the built-in `leanchecker`; the former standalone `lean4checker` project
is deprecated. A first `lake env leanchecker --fresh MirRegionFrame` attempt
terminated without retained tool output, so it is inconclusive and is not
counted as evidence. `nanoda` is not installed.

A receipt-owning runner now invokes built-in `leanchecker --fresh`, preserves
exit status/output/version and actual checker binary hashes, rejects unsafe
module names, and fails closed on timeout, missing tools, lost output, or
rejection. Unblock condition: provision and pin the independent
`lean4export`/`nanoda` adapter, run both receipts against one artifact, and
require their closure to agree with the Lean 4.33 axiom audit.
The common assurance layer now owns the typed replay schema. Contract and
release promotion validate the exact accepted closure hash and artifact
identity, so an arbitrary nonempty `independent_replay_hash` no longer passes.
The pinned setup gate exists and correctly rejected the deployed Rust seed
with exit 2 before provisioning. Once a genuine self-hosted compiler is
deployed, it builds reviewed lean4export/nanoda commits and the repository
adapter, whose closed policy rejects both `sorryAx` and `Lean.trustCompiler`.
Built-in `leanchecker --fresh KernelCapabilities` was also attempted after a
successful Lean build; it emitted no output and exited 124 at 60 seconds. The
runner therefore correctly has no accepted fresh receipt yet.

## Remaining product refinement blockers

The SimpleOS Lean projects remain `model_proven` until a SymbolId- and
semantic-hash-bound source-to-model adapter is checked. The generated RISC-V
product remains placeholder-rejected at
`src/lib/hardware/fpga_linux/riscv_fpga_linux.spl` until a real generated RV32I
retirement path, RVFI evidence, covers/mutations, HWIR-to-RTL checking, and
netlist identity exist.

The capability-rights audit found and repaired two false-assurance defects:
its named Lean theorem did not exist, and raw caller-provided audit text could
directly return `source_refined`. The theorem now exists and checks with only
`propext`/`Quot.sound`; raw evidence tops out at `model_proven`, while typed
promotion requires exact proof, independent replay, artifact, and exhaustive
source/model behavior hashes. Scheduler review also found the Lean model
preserved `park_reason` while Simple cleared it; the Lean transition and four
audited theorems now match. The remaining IPC/storage/unmap raw validators were
downgraded to `model_proven` pending the same typed promotion conversion.

The bounded RV32 ADD audit likewise found that caller-constructed formal job
objects could report `model_proven` without executing SBY. They now report
only `specified`. The external receipt path is additionally bound to the exact
module, HWIR, RTL, RVFI contract, assumption manifest, generated inputs,
outputs, and engines. A pure-Simple bundle generator and end-to-end SBY gate
were added; the gate correctly exits 2 before generation with the deployed
Rust seed. SBY/Yosys/GHDL/Boolector are installed, while Sail is absent. The
existing pinned Sail Zca classification gate passes but explicitly provides no
ADD semantic-equivalence evidence.

Unblock condition: satisfy Gates 4 and 5 in
`doc/04_architecture/simple_formal_verification_2_0.md` without weakening the
existing fail-closed scripts.
