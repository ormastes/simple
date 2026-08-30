# RISC-V Gen2 Qualification Receipt Is Not an Adversarial Provenance Boundary

Date: 2026-08-12

Status: open — release blocker for mission-critical qualification

## Observation

The receipt composer retains hash-bound evidence created by the fixed
qualification runner and producer, but its public manifest format remains
serializable. A caller able to modify repository-controlled scripts or invoke
the composer directly can manufacture internally consistent files, hashes, and
zero exit fields. This is not a cryptographic attestation boundary.

The runner/producer separation is an interface convention, not an OS capability
boundary: both execute under the same UID and the producer can inspect the
final-evidence path. The final run directory is fresh and hash-bound, not
immutable: the current ordinary directory/copy/write operations do not pin a
descriptor, lock it, or prevent later replacement.

The latest qualification envelope narrows the normal path: it pins the
repository producer, builds VHDL and receipt entry closures with the admitted
Stage-4 compiler, and executes target-specific RV32 C.JAL/RV64 C.ADDIW plus
C.EBREAK GHDL probes. Those properties are necessary operational evidence, not
proof against a hostile filesystem or same-repository writer.

## Containment

- `qualification_receipt.json` must not promote a Gen2 product to
  mission-critical or release-qualified status by itself.
- The receipt remains valid only as a controlled-run artifact after external
  review of the admitted repository revision, runner/producer bytes, GHDL
  binary identity, logs, and retained sidecars.
- Bootstrap-seed output and a manually supplied manifest remain non-evidence.

## Required closure

1. Bind runner, producer, coverage-spec, generated testbenches, and exact GHDL
   binary/version hashes into the retained receipt; invoke GHDL by canonical
   path. **Implemented for the controlled-run envelope; it is not an
   authorization capability.**
2. Retain and parse the raw coverage SDN, recompute basis points, and validate
   it against a complete owned-Gen2 decision inventory. The retained SDN is
   now parsed and recomputed, and every current owner must contribute a
   decision row. The inventory/denominator closure remains open; dependency or
   missing-owner decisions must not satisfy the threshold.
3. Replace check/hash/copy path sequences with descriptor-relative no-follow
   operations (`openat`/`O_NOFOLLOW`/`O_EXCL`) for hostile-filesystem claims.
   This requires a bounded runtime snapshot primitive that pins source and
   destination directory descriptors, hashes while copying, rechecks source
   identity, fsyncs, and publishes without replacement.
4. Add a signed or externally authenticated qualification attestation if the
   project requires a security boundary rather than controlled-process
   provenance.
5. Retain and hash the exact derived VHDL and receipt entry binaries, their
   native-build and post-bootstrap gate logs, and each product compile log.
   Recheck the admitted source revision after those builds and bind the result
   to the receipt before claiming the derived executables came from that
   revision.

## Required coverage-inventory design

Do not derive a release denominator from an observed runtime SDN. Runtime
captures contain only reached decisions. The current exact-owner presence gate
prevents a one-owner report from silently claiming the whole scope, but it does
not prove decision completeness.

The closure requires a compiler-emitted, zero-count decision manifest for the
exact instrumented source closure, followed by a reviewed source-controlled
inventory. A candidate inventory may be calibrated only from an admitted run;
it is non-promoting until reviewed and checked in. Each stable entry must bind
an owner, relative path, source hash, source anchor, ordinal, and outcome.
The producer and receipt composer must then require exact key-set equality
between the manifest, inventory, and executed counters, retain and hash all
three inputs, and calculate the denominator from the inventory. Exclusions, if
ever needed, require a versioned reason, anchor, expiry, and review.

The runtime already accepts a compiler decision-manifest block, but the
compiler does not yet emit one. The missing compiler phase must deterministically
emit every discovered decision with zero/zero counters before lowering and
reject duplicate or out-of-closure sites. A calibrator may produce only a
non-promoting candidate inventory under `build/calibration/`; it must use that
zero-count manifest, source hashes, anchors, occurrences, and ordinals, never
an observed runtime stream. Promotion is a separately reviewed source change
that pins the reviewed inventory hash in the coverage scope.

This is not an emitter-only patch. Pure-Simple MIR currently has no
`DecisionProbe`/`ConditionProbe` opcode or coverage lowering, current
interpreter probe IDs are load-order-dependent arena indices, and AST spans do
not preserve a stable module-file identity. The coordinated implementation must
add typed stable site keys to MIR; lower `if`, loop, and compound-condition
sites with module path, line, column, and deterministic ordinal; lower those
opcodes through native backends to the existing runtime counters; and scan the
finalized pre-optimization MIR closure to render one sorted zero-count SDN
block. Compilation must reject duplicate keys, missing paths/spans, or a
lowered branch lacking a registered site. Source-text scanning and observed
runtime SDN are prohibited substitutes.

Freeze the first implementation as `MirCoverage*V1`: an explicit lowering
mode, source-bound decision/condition site keys, observational probe opcodes,
and one deterministic finalization pass before MIR optimization. The first
language slice is `if`, `while`, and short-circuit atomic predicate leaves.
Probe identities must derive from an authored repository-relative source path,
canonical function name, byte spans, kind, and source-preorder occurrence; the
finalizer sorts rather than iterating maps, allocates runtime IDs only after
sorting, validates exact source/anchor hashes, and emits zero/zero SDN tables.
The HIR pipeline must first propagate `source_file_authored_path`—current
`Span.file` is insufficiently reliable. Backends must lower finalized probes to
existing runtime counters or fail explicitly; DCE/CSE must preserve their order.

The opcode landing is a multi-owner fail-closed change. First add typed
observational variants with exact canonical MIR JSON serialization, operand
visitor support, explicit DCE side-effect/use handling, and tests proving both
LLVM paths, MIR interpreter, SSA, inlining, and verification regions reject a
probe-bearing function rather than skipping it. Current JSON collapses unknown
instructions to `UnsupportedInst` and both LLVM paths can silently erase
unknown variants; neither behavior may remain once probes exist. Only after
the closure finalizer resolves every provisional key one-to-one against the
catalog may lowering emit probes. Runtime calls, optimizer rewrites, and
publication follow as separate enabled phases.

## Required evidence-transaction design

The current path-based no-follow checks are insufficient for a hostile local
filesystem: later reads, hashes, and copies reopen the pathname. Add a narrow,
fail-closed runtime snapshot transaction before treating the receipt as an
authority boundary. It must pin source and destination-directory descriptors,
copy a bounded regular source with `O_NOFOLLOW` into an `O_EXCL` temporary,
recheck the source identity, fsync file and directory, and atomically publish
without replacement. Parse and hash only the retained snapshot. Windows must
reject as unsupported until an equivalent handle-relative implementation exists.

Do not land this central ABI work in the shared Gen2 migration tree. Its
minimal path-only snapshot still touches the C runtime, Rust/interpreter
registrations, ABI tables, capability whitelists, and duplicate-symbol gates.
Land and admit it from a clean dedicated worktree first; then integrate the
receipt as a separate change. A stronger follow-up must bind a trusted directory
descriptor and a relative path, because leaf-only `O_NOFOLLOW` does not pin
ancestor directories.

Until these conditions and the admitted Stage-4 RV32/RV64 run are complete,
the qualification state remains development-stage and fail-closed.
