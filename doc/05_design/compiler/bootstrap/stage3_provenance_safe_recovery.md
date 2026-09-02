<!-- codex-design -->

# Stage 3 provenance-safe recovery after terminal failure

Date: 2026-09-02

## Scope

This design recovers Stage 3 from an already admitted pure-Simple Stage 2
lineage after a terminal Stage 3 failure. It does not authorize or execute a
restart, Stage 4, deployment, release, cache deletion, or receipt fabrication.

The recovery must preserve four independent authorities:

1. the exact Stage 2 compiler bytes;
2. the immutable Stage 2 admission evidence;
3. the source, runtime, tool, backend, and ABI-policy snapshot to compile; and
4. a canonical planner-v2 receipt targeting `//bootstrap:stage3`.

## Current evidence

### Failed isolated lane

The former isolated Stage 3 lane under
`/private/tmp/claude-501/-Users-ormastes-simple/fc0cc01f-ce01-4f4c-b58e-5a2f14222318/scratchpad/s3-wt`
is not reusable as preserved Stage 3 authority:

- the failed Stage 3 log records `E-MIR-TYPE-ZeroKind` while lowering
  `compiler.driver.pipeline_fn.compile_specialized_template_release` and a
  native-build worker exit code of `1`;
- no Stage 3 candidate or `simple-bootstrap-stage3-provenance-v4` manifest was
  published;
- later Stage 2 attempts reused that output tree, removed the earlier admitted
  Stage 2 paths, and produced a newer `No space left on device` failure; and
- PID `17195` currently owns that scratch output through a distinct
  `--full-bootstrap --stop-after-stage2` transaction.

Therefore the scratch output is writer-owned and tainted until that producer
is terminal and its own new Stage 2 transaction either converges or fails. No
file from it may be copied into a recovery lane while the producer is live.

### Preserved main-worktree Stage 2 bytes

The last preserved pure-Simple Stage 2 bytes are identical at all three paths:

| Role | Path | SHA-256 |
|---|---|---|
| Produced parent | `build/bootstrap/stage2/aarch64-apple-darwin/simple` | `b156a85422c0224fef68c8a36456ef61f68c99761f5858e88b84291e9ad3e62a` |
| Admitted parent | `build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple` | `b156a85422c0224fef68c8a36456ef61f68c99761f5858e88b84291e9ad3e62a` |
| Immutable backup | `build/phase_snapshots/phase1_1788229858_phase2_1788229942/simple` | `b156a85422c0224fef68c8a36456ef61f68c99761f5858e88b84291e9ad3e62a` |

The phase snapshot is backup bytes only. It is never parent authority by
itself and must not be executed merely because its digest matches.

The admission binds these immutable snapshots:

| Evidence | SHA-256 |
|---|---|
| Stage 2 admission | `416d6f521ebe09c4817360daf6ecf99358ba8bb2d96c3f630b97c78da26dece7` |
| Source snapshot | `2aa73a93ca018e4f79fd773f09cbe7ecb333700f7700f3785877641f48794d92` |
| Runtime snapshot | `148c6451cea8468675eeb80fb0758534d79c3fc49a5237e12e08069d52b9d4ae` |
| Tool authority | `cde0c3286d4fa3d4fac3a93a1936de3353ad8b962ed64285e0aae7892e490be8` |

This tuple is not currently closed authority. Both top-level Stage 2 parent
receipts bind the older admission digest
`9e43ec9b01b4df199a22174bcf0fd961a88fc5fcda9fdd734ff8578ee8d2ac03`,
not the live admission digest `416d6f...`. The admitted Git head is
`1de6e3135f4cf9335bb04bc3546bfca36d138768`, while the current worktree head is
`c846dc3c074d03392b7f2041fa7e74290a67a925`. A direct resume must therefore
refuse before acquiring the output lock.

The existing planner receipt `adm-m.receipt` passes the current planner-v2
shape/binding verifier and names the `b156...` parent, but it does not repair
the stale admission digest inside the parent receipts. It cannot independently
close the recovery lineage.

## Canonical parent authority

The canonical Stage 2 parent is a tuple, not a preferred executable path:

```text
Stage2AuthorityV1 = {
  produced_compiler,
  admitted_compiler,
  immutable_phase_snapshot,
  stage2_sanity_receipt,
  stage2_provenance_receipt,
  stage2_admission_receipt,
  source_snapshot,
  git_snapshot,
  runtime_authority,
  runtime_snapshot,
  tool_authority_snapshot,
  stage2_command_transcript,
  backend,
  abi_policy
}
```

Authority exists only when all of these predicates pass in one canonical Git
worktree and one output lineage:

- produced, admitted, and backup compiler bytes have the same expected digest;
- sanity, provenance, and admission receipts each have an exact key set and
  re-hash every file they name;
- sanity and provenance receipts bind the current admission receipt digest;
- the admission receipt binds the exact source/runtime/tool/sanity/receiver
  digests, build arguments, hosted runtime, backend, and explicitly selected
  ABI policy;
- a fresh source/Git/runtime/tool snapshot is byte-identical to the admitted
  snapshot before any output lock or cleanup;
- the planner-v2 receipt verifies canonically, targets `//bootstrap:stage3`,
  and binds both the produced and admitted compiler paths to the same digest;
  and
- no process owns the selected output/cache lineage.

Changing a receipt in place is forbidden. If any predicate fails, create a new
admission generation through the canonical Stage 2 producer. The phase snapshot
may supply recovery bytes only through such a new admission transaction.

## Recovery state machine

### R0 — Preserve terminal evidence

Retain the failed log, command transcript, status receipt when present, memory
and phase profiles, native objects, and cache directory. Record their digests
before any later transaction. Never interpret loose native objects as a
candidate or cache authority.

### R1 — Exclude live writers

Resolve the canonical source root, output root, output lock, and every process
whose CWD or command names that output. A live owner produces `PENDING`; it does
not trigger a kill, wait loop, restart, receipt write, or candidate inspection.

### R2 — Select one parent lineage

Prefer a newly converged isolated Stage 2 transaction over repairing a stale
main-worktree tuple. If the active scratch Stage 2 transaction fails, preserve
its evidence and do not merge its files with the `b156...` tuple.

The `b156...` tuple may be reused only after a canonical re-admission binds the
chosen frozen source tree, runtime, tools, backend, ABI policy, and exact live
admission digest. A matching binary hash alone is insufficient.

### R3 — Freeze source and capacity

Use an isolated worktree whose source bytes no longer change during recovery.
The current source snapshot must match the admission exactly. The snapshot file
is a digest inventory, not a source backup; it cannot reconstruct missing dirty
bytes. If the original bytes are unavailable, create a new Stage 2 admission
against the intended frozen source instead of claiming the old snapshot.

Before authorization, require an operator-supplied minimum free-byte value
derived from the retained build's measured peak. There is no silent default.
This makes the prior disk-exhaustion failure fail closed without inventing an
unselected capacity target.

### R4 — Mint planner authority

Only the canonical pure-Simple planner producer may emit the receipt. The
receipt target is `//bootstrap:stage3`; the reason is
`verify-landed-compiler-fix`. Re-run all authority guards after receipt
creation because the receipt does not supersede Stage 2 admission checks.

### R5 — Continue Stage 3 once

The continuation must use `resume-stage3-from-admitted.sh`, the exact admitted
parent, the phase-owned Stage 3 cache, `SIMPLE_NO_STUB_FALLBACK=1`, and a new
evidence interval. It must preserve the old failure evidence before replacing
any Stage 3 transient file. A failed continuation publishes a terminal status
receipt and removes candidate/sanity/provenance outputs.

### R6 — Observe, never deploy

After the producer is terminal, run `guard-existing-stage3-deploy.shs
--observe`. Success means only that the Stage 3 candidate and provenance-v4
manifest are admitted. Stage 4 still needs a separate planner-v2 receipt.
Deployment remains a distinct, explicitly authorized transaction.

## Required guard surface

Add a non-mutating preflight mode before any recovery is executed:

```text
scripts/bootstrap/check-stage3-recovery-authority.shs
  --source-root=PATH
  --output-dir=PATH
  --planner-receipt=PATH
  --expected-parent-sha256=HEX64
  --expected-source-snapshot-sha256=HEX64
  --minimum-free-bytes=N
```

It emits exactly one terminal receipt:

```text
schema=simple-bootstrap-stage3-recovery-preflight-v1
status=pass|pending|refused
reason=...
source_root=...
output_dir=...
parent_sha256=...
stage2_admission_sha256=...
source_snapshot_sha256=...
runtime_snapshot_sha256=...
tool_authority_sha256=...
planner_receipt_sha256=...
backend=...
abi_policy=...
free_bytes=...
minimum_free_bytes=...
```

The guard must not acquire the bootstrap output lock, delete/copy artifacts,
run a compiler, mint planner/Stage3 receipts, or inspect a live candidate. It
returns `3` for a verified live owner, `0` only for a complete authority tuple,
and nonzero for every mismatch.

`resume-stage3-from-admitted.sh` must gain `--preflight-only` or consume and
re-derive this exact receipt before lock acquisition. The production resume
must bind the preflight receipt digest into its command transcript and Stage 3
status/provenance receipts so a different source or parent cannot be swapped
between preflight and execution.

## Guard commands

These commands are design-time/operator commands. They were not executed as a
restart or deployment by this lane.

### Detect a live output owner

```sh
SOURCE_ROOT=/absolute/frozen/worktree
OUTPUT_DIR="$SOURCE_ROOT/build/bootstrap-recovery"
ps -axo pid=,ppid=,etime=,state=,command= |
  grep -F -- "$OUTPUT_DIR"
```

Any matching bootstrap/native-build writer makes the lane `PENDING`. Confirm
its CWD with `lsof -a -p "$PID" -d cwd -Fn`; a PID number alone is not identity.

### Verify existing planner authority without execution

```sh
cd "$SOURCE_ROOT"
. scripts/check/lib/bootstrap-planner-admission-bound.shs
bootstrap_planner_v2_verify "$STAGE3_PLANNER_RECEIPT" "$SOURCE_ROOT"
bootstrap_planner_v2_verify_parent_compiler_binding \
  "$STAGE3_PLANNER_RECEIPT" \
  "$OUTPUT_DIR/stage2/aarch64-apple-darwin/simple" \
  "$OUTPUT_DIR/stage3/aarch64-apple-darwin/stage2-admitted/simple"
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-stage3-from-admitted="${OUTPUT_DIR#"$SOURCE_ROOT"/}" \
  --bootstrap-receipt="$STAGE3_PLANNER_RECEIPT" \
  --validate-bootstrap-receipt
```

### Reject the current stale admission closure

```sh
ADMITTED="$OUTPUT_DIR/stage3/aarch64-apple-darwin/stage2-admitted/admission.env"
SANITY="$OUTPUT_DIR/stage2/aarch64-apple-darwin/stage2-sanity.receipt"
PROVENANCE="$OUTPUT_DIR/stage2/aarch64-apple-darwin/stage2-provenance.receipt"
LIVE_ADMISSION_SHA=$(shasum -a 256 "$ADMITTED" | awk '{print $1}')
test "$LIVE_ADMISSION_SHA" = \
  "$(sed -n 's/^admission_receipt_sha256=//p' "$SANITY")"
test "$LIVE_ADMISSION_SHA" = \
  "$(sed -n 's/^admission_receipt_sha256=//p' "$PROVENANCE")"
```

Both comparisons are mandatory. The current main-worktree tuple fails them and
must not be resumed.

### Produce a new Stage 3 planner receipt after authority converges

```sh
cd "$SOURCE_ROOT"
sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
  --root="$SOURCE_ROOT" \
  --bootstrap-output="$OUTPUT_DIR" \
  --target=//bootstrap:stage3 \
  --reason=verify-landed-compiler-fix \
  --parent-compiler="$OUTPUT_DIR/stage2/aarch64-apple-darwin/simple" \
  --runtime-dir="$OUTPUT_DIR/stage3/aarch64-apple-darwin/stage2-runtime-authority" \
  --out="$OUTPUT_DIR/stage3-planner-admission-v2.env"
```

This command is not a Stage 3 restart, but it creates authority and therefore
must run only after R1-R3 pass.

### Future Stage 3 continuation — intentionally not run

```sh
cd "$SOURCE_ROOT"
env \
  SIMPLE_ABI_POLICY='<selected: compat-deferred|v1>' \
  SIMPLE_KERNEL_K1_POLICY='<selected: llvm-cranelift|cranelift-only>' \
  SIMPLE_BOOTSTRAP_REASON_RECEIPT="$OUTPUT_DIR/stage3-planner-admission-v2.env" \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
    --resume-stage3-from-admitted="${OUTPUT_DIR#"$SOURCE_ROOT"/}" \
    --bootstrap-receipt="$OUTPUT_DIR/stage3-planner-admission-v2.env"
```

Do not add `--fresh-cache`; the phase-owned cache is preserved unless a
specific stale-cache defect is proven. Do not run this command until the
recovery preflight guard exists and passes.

### Future terminal observation — no deployment

```sh
sh scripts/bootstrap/guard-existing-stage3-deploy.shs \
  --pid="$RECOVERY_PRODUCER_PID" \
  --source-root="$SOURCE_ROOT" \
  --output-dir="$OUTPUT_DIR" \
  --observe
```

Never substitute `--admit-deploy` in this recovery lane.

## Failure handling

| Condition | Required result |
|---|---|
| Live writer owns output | `PENDING`; no artifact inspection or mutation |
| Parent/admitted/snapshot digest differs | `REFUSED`; select one lineage |
| Parent receipt binds stale admission digest | `REFUSED`; new admission generation |
| Source/Git/runtime/tool snapshot differs | `REFUSED`; freeze or re-admit |
| ABI or K1 policy is unselected | `REFUSED`; no default selection |
| Planner receipt is absent/stale/wrong target | `REFUSED`; canonical producer required |
| Free-space requirement is absent or unmet | `REFUSED`; preserve evidence |
| Stage 3 exits nonzero or has no executable | publish failure status; remove candidate manifest |
| Candidate exists without valid provenance-v4 | reject and quarantine; never deploy |
| Stage 3 converges | observer may report `stage3-admitted`; stop |

## Verification design

Add shell/SPipe coverage for:

1. exact current tuple passes all bindings;
2. each of parent, admission, source, runtime, tool, backend, ABI policy, and
   planner digest mutations fails independently;
3. the current stale `9e43...` versus `416d...` admission relationship fails;
4. phase-snapshot-only input fails;
5. a live matching writer returns `PENDING` without reading candidate bytes;
6. a reused PID with wrong CWD/command fails;
7. missing minimum free bytes and insufficient free bytes fail;
8. `--preflight-only` creates no lock, cache, candidate, or receipt;
9. a failed continuation preserves prior evidence and publishes only a failed
   status receipt; and
10. observation never invokes Stage 4 or deployment.

Runtime execution evidence remains blocked until an authority tuple passes this
design. Structural review alone must not be reported as a successful recovery.

## Acceptance criteria

- One canonical Stage 2 authority tuple passes every re-derived binding.
- The source worktree is immutable for the recovery interval.
- A Stage3-target planner-v2 receipt binds that exact tuple.
- The non-mutating recovery guard passes and its digest is bound into the
  eventual Stage 3 transcript and provenance.
- Stage 3 is attempted at most once for that authority tuple.
- A successful candidate has a valid provenance-v4 manifest and passes
  `--observe`.
- No Stage 4, deployment, or release action occurs in this lane.
