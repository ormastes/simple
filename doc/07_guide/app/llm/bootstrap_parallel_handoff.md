# Bootstrap Parallel Handoff

This is the operator contract for handing a bootstrap candidate from the x86_64
Linux lane to platform owners. Parallel work is allowed, but evidence is
lineage-bound and platform claims remain fail-closed.

## Diagnostic continuation before full qualification

Use the [shared build collection policy](../../tooling/bootstrap_failure_collection.md)
for the active operator workflow. Finish all independently runnable modules and
tests, retain every failure, and assign independent causes to parallel repair
agents. Keep their writable sources, caches and outputs isolated.

An immutable producer may launch the next provisional phase after it compiles
Hello World and the resulting executable passes its output/exit check. Record
both commands and hashes. Full verification may continue in parallel; this
provisional handoff does not satisfy the formal readiness checker below.
Binary existence or `--version` alone is insufficient.

For a user-authorized time, memory or policy exception, record the disabled
check and retain resource/progress monitoring in a separate DIAGNOSTIC lineage.
Do not silently retain an enclosing kill threshold the user disabled. Missing
inputs and actual failed operations remain failed or blocked. Restore normal
gates before admission or promotion. The next actual restart integrates latest
requested release and reviewed applicable unmerged fixes; preserve live frozen
inputs, old receipts and compatible frontend/HIR caches.

## Canonical readiness checker

Run the canonical checker for the exact target triple:

```bash
sh scripts/check/check-bootstrap-platform-handoff-readiness.shs
```

The checker reads receipts; it does not manufacture evidence. It rejects stale
artifacts, seed or cross-build substitutions, missing logs, missing rollback
output, mismatched source/candidate hashes, and partial marker output. It emits
`PASS` only after all required gates and the selected platform handoff are
complete. An unavailable host is `OPEN` or `BLOCKED`, never `PASS`.

## Ownership and permitted parallel work

The Stage 3 owner may be another agent. That owner supplies the admitted Stage 3
path, SHA-256, authority/compiler identity, rejection-probe result, frontend
admission, and source revision for a formal handoff. Stage 4 and platform agents may prepare
diagnostics, preserve caches, review receipts, and arrange external native hosts
without waiting for the Stage 3 process to finish. This is independent
preparation, not admission. They may also execute provisional work after the
Hello gate above; no agent may claim a later formal gate until it has consumed
the required receipt for the same source lineage.

The merge owner freezes the candidate and is the only agent that publishes the
combined readiness result. A final reviewer checks the frozen receipts before a
release or platform claim.

## Producer-bound incremental tool caches

Keep compiler-capsule caches separate from tool-closure caches. For every
requested compiler generation, build the full CLI and test runner with distinct
writable caches:

```text
build/bootstrap/tool_cache/
  phase2/<compiler-sha>/{full-cli,test-runner}/
  phase3/<compiler-sha>/{full-cli,test-runner}/
  phase4/<compiler-sha>/{full-cli,test-runner}/
```

Each producer directory must retain the compiler SHA-256, frozen source
revision, entry path, target, backend, runtime authority, and exact argv. Reuse
the same directory for incremental retries of that lineage. Never let parallel
writers or different compiler hashes share a cache.

`bootstrap-phase-verification.shs` freezes a phase-qualified command-owner
receipt beside the two built tools. The receipt binds the phase, exact full CLI
standalone runner, and MCP server paths and SHA-256 values. Every check and test
validates the receipt and all three tools before and after execution, and test subprocesses receive
`SIMPLE_BINARY=<that full CLI>`. A runner must never select itself or an ambient
deployed compiler as its child command owner. Same-lineage retries may reuse an
identical frozen receipt; a changed tool pair receives a hash-qualified receipt.

Phase verification runs representative compiler bootstrap and MCP behavior in
both `--mode=interpreter` and `--mode=compile`. A native build of the runner is
build evidence only; it does not establish compiled test execution. Full
compiler inventory rows remain distinct from the repository-wide Stage 6
`test test --whole --mode=interpreter` release gate.

For an admitted Phase 3 or Phase 4 compiler, `--strategy=full` also freezes a sorted
inventory of every `test/**/*_spec.spl` and `test/**/*_test.spl` file and
terminalizes each row through
the requested phase's built runner with its exact full CLI owner. Every row uses isolated
interpreter execution with `--assert-ran`, caches and the session daemon
disabled. MCP rows also receive the receipt-bound `SIMPLE_MCP_TEST_BINARY`; no
inventory row may use a deployed `bin/simple_mcp_server`. Each row retains JSON counts and must report at least one executed
example; skipped-only success is rejected. The receipt records total, passed,
timeout, and crash counts; an empty inventory, a skipped command owner, a
timeout, a crash, a discovery error, or any nonzero row makes
the phase full-test result fail. Phase 4's inventory is a Stage 4 gate and does
not replace release testing.

Stage 2 and Stage 3 `bootstrap_main` artifacts are intentionally compiler-only.
They can native-build self-running specs but do not expose suite discovery. Run
`test test --whole --mode=interpreter` only with the non-vacuous full CLI built
by the requested producer. A zero exit without a `Results:` line is vacuous and
must fail the gate. Phase 4 repeats the two tool builds with Phase 4 as producer
before self-host or release claims; a Phase 3-built tool does not prove a Phase
4-produced tool. It also freezes a Stage 4 tooling receipt that binds the
admitted compiler snapshot, hosted runtime authority, Phase 4 CLI/runner
receipt, and MCP/LSP server hashes. Stage 4 MCP integration and both server help
probes validate this receipt before and after execution. Phase-qualified cache
and output paths keep Phase 3 artifacts outside the Stage 4 evidence namespace.

## Historical x86 transaction status (2026-08-14)

The session-specific retry restrictions below describe that historical run;
they do not cancel a later user's explicit diagnostic-continuation instruction.

Historical cycle 3 repaired two source frontiers and published Stage 2,
binary SHA-256
`e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`,
log SHA-256
`db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`.
At 09:52:45 host `earlyoom` sent Stage 3 SIGTERM at 41,394 MiB RSS with less
than 10% free memory and no swap; exit 143 followed 5.4 seconds later. The
empty log hashes to
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
That parent predates the complete `d99deb3` memory-snapshot runtime provider;
41,394 MiB is an interrupted high-water mark, not a proved completion budget.
The current authority is
`doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`:
Phase 2 parser versus Phase 3 HIR retention is unresolved. TODO666 is
open/actionable: the incompatible M0 draft was reverted; existing resume-only
durable sinks remain, while safe phase publication, full-bootstrap wiring,
process/RSS/signal supervision, and provenance migration. After M0 acceptance,
build a fresh current-HEAD Stage 2 and run one instrumented Stage 3 in a fresh session. No fourth run is permitted in
this session. TODO667 remains gated.

## Formal Gate 1-7 sequence

Run and record these in order. Do not skip a gate or restart with a different
candidate between gates.

1. **Gate 1, Stage 3 admission:** after M0 acceptance, run a fresh unique-output
   current-HEAD Stage 2 plus one instrumented Stage 3; retain phase, memory,
   process-group, RSS, exact identity, rejection probe, frontend admission,
   path, manifests, and SHA-256.
2. **Gate 2, x86_64 Linux Stage 4:** build the non-stub pure-Simple candidate
   from the Gate 1 lineage and retain build/progress/RSS receipts.
3. **Gate 3, candidate sanity/hash:** freeze the candidate path and SHA-256;
   record identity, provenance, no-stub/no-failure scan, sanity output, and
   unsupported-command behavior.
4. **Gate 4, essential-tools smoke:** the canonical transaction invokes
   `check-bootstrap-essential-tools-smoke.shs` internally exactly once. Retain
   `stage4-essential-tools-smoke.log` and all four markers; do not repeat a
   standalone smoke against the same candidate.
5. **Gate 5, deployment:** deploy only that candidate and retain the pre/post
   identities. Keep this source-matched authority deployed through Gate 6
   unless TODO667 publishes an isolated immutable bundle that downstream rows
   execute directly.
6. **Gate 6, platform acceptance/handoff:** the platform owner runs the exact
   native, QEMU, target, or scoped matrix command for the selected row and
   returns host identity, toolchain, source/compiler hashes, artifact hashes,
   logs, sanity, and essential-marker receipts.
7. **Gate 7, rollback:** only after all selected Gate 6 evidence, run
   `sh scripts/bootstrap/rollback-bootstrap-deploy.shs <canonical-triple>`.
   Retain the command, exit status, receipt path, restored hash, and
   post-rollback arithmetic smoke. An earlier rollback is valid only when
   Gate 6 ran from TODO667's isolated immutable bundle. Publication of that
   bundle binding candidate, deploy receipt, pre-deploy binary, rollback
   script/receipt, downstream receipts, and hashes remains the TODO667 gap.

After Gate 7, invoke the helper step named exactly
`step_bootstrap_platform_handoff_readiness`. It invokes the canonical checker,
selects the Gate 6 row, and records the handoff status. It cannot waive or
reorder Gates 1--7.

## External native-host handoffs

Linux AArch64, macOS, Windows, and hosted RISC-V rows require their stated
native host or explicitly scoped environment. The handoff package must name the
owner, reviewer, host identity, toolchain versions, exact command, source and
compiler hashes, artifact paths and hashes, logs, sanity output, and markers.
Cross-compilation, x86 QEMU, a stale artifact, or a host that was not available
is not native-host PASS. The row remains open with its unblock condition.

## No false PASS and the three-cycle cap

`PASS` means the evidence exists for the exact candidate and every required
receipt is internally consistent. Executable existence, zero failed files,
static checks, frontier review, preparation work, or a successful unrelated
platform cannot be promoted to PASS. Missing or empty guest/native logs fail the
claim.

For a failing live run, stop at the first trustworthy boundary, preserve the
receipt, fix the pure-Simple owner, and verify a distinct root-cause cycle. The
lane has a maximum of three distinct fix/verify cycles. Do not rerun an identical
failed command; after the third cycle, stop and report the remaining blocker.

## Hello sanity: 16 native execution cases and phase interpreter checks

The complete native Hello target is a 16-case matrix: four linkage forms, two
code-generation backends (LLVM and Cranelift), and two execution paths (direct
compiler invocation and BuildRunner). The forms are: source to executable,
two objects to executable, static library to executable, and shared library to
executable. Every cell must build and run its own executable and retain the
observed `Hello, World!` output. A successful compile, object, or library build
alone is not a pass. Do not substitute frontend probes (`p2_add`, MIR retention,
module naming, or positional Hello) for these cases.

Track each cell independently using the tuple `(form, backend, path)` and one
of `PASS`, `FAIL`, `UNRUN`, or `UNSUPPORTED`, with command, compiler identity,
artifact hash, exit status, and output as evidence. A missing receipt is
`UNRUN`; unsupported behavior is never a pass. The required rows are:

| Form | LLVM direct | LLVM BuildRunner | Cranelift direct | Cranelift BuildRunner |
| --- | --- | --- | --- | --- |
| Source to executable | status + evidence | status + evidence | status + evidence | status + evidence |
| Two objects to executable | status + evidence | status + evidence | status + evidence | status + evidence |
| Static library to executable | status + evidence | status + evidence | status + evidence | status + evidence |
| Shared library to executable | status + evidence | status + evidence | status + evidence | status + evidence |

These are acceptance requirements, not claims that all 16 cases are currently
implemented or proven. At the time of this guide update, the existing
`hello-sanity-matrix.py` driver runs the four direct cases for one selected
backend per invocation. An optional one-source BuildRunner adapter requires
`--buildrunner-manager`, `--buildrunner-manifest-writer`,
`--buildrunner-template`, and `--buildrunner-target` together. It uses the
production manifest writer and manager, verifies the published artifact and a
bound enforced-memory receipt, then executes the artifact. Manager exit alone
is insufficient. Its memory receipt support is currently limited to Windows
Job Objects and Linux cgroups; macOS cannot receive a BuildRunner pass from an
unqualified memory receipt. The other three BuildRunner forms remain `UNRUN`.
Without the complete provider configuration, all four BuildRunner forms remain
`UNRUN`. Keep separate reports for both backends. Required pending BuildRunner
cells make an otherwise successful direct report `PARTIAL` with nonzero exit;
neither a report nor this guide claims the full 16-case gate has passed.

Invoke `scripts/bootstrap/hello-sanity-matrix.shs` from Bash or the
`hello-sanity-matrix.cmd` entrypoint from Windows with `--compiler`,
`--phase 1|2|3`, `--source-root`, `--runtime-path`, a fresh `--output`, and
`--backend llvm|cranelift`. Use the exact compiler belonging to the phase and
backend being checked. Keep outputs and logs distinct; parallel jobs may share
frozen read-only inputs but must not share writable outputs or conflicting
caches. Record compiler/runtime identities, link inputs and commands, exit
statuses, artifact hashes, and observed output. Backend reports remain
diagnostic evidence and do not replace formal admission receipts.

On macOS the adapter pins the actual clang binary and `ld64.lld`, captures
the compiler's hosted link inputs, checks exact main/provider object identity,
and verifies the shared library load command and exported symbol. The default
is serial execution (`--jobs 1`); `--jobs 0` permits concurrent direct lanes
only when aggregate resource headroom allows it. `--max-rss-kib` bounds each
command's process tree, and `--min-free-disk-bytes` defaults to 1.5 GiB. Admission
must also preserve the campaign's host memory reserve; a request for parallel
cases does not authorize exceeding it.

The 2026-10-29 macOS diagnostic campaign used the unchanged P2 compiler
`0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
All eight direct cells (four per backend) terminated at their RSS bounds before
emitting their requested artifacts. Their process receipts report quiescence
and zero observer errors. All eight BuildRunner cells were `UNRUN`; the P2
interpreter was `SKIPPED`. The native matrix is **incomplete and failing**.
Retained local evidence is under
`build/hello-matrix-macos-p2-cranelift-20261029-02` and
`build/hello-matrix-macos-p2-llvm-20261029-01`; the latter contains the resource
admission record showing capacity for one lane after the 8 GiB host reserve.
Real C-based Mach-O transport tests validate the adapter's four linkage forms;
they are not evidence that these P2 Simple compiler cells passed.

Interpreter execution is tracked separately from the 16 native cases. Use the
interpreter owned by the selected phase compiler; a separate or ambient CLI is
not evidence. The phase-specific interpreter state is:

| Phase | Interpreter requirement | Evidence rule |
| --- | --- | --- |
| 1 | Required | Run the seed's `run` with `SIMPLE_EXECUTION_MODE=interpret`; bind evidence to the phase 1 compiler. |
| 2 | Configured skip | Minimal compiler has no `run`; record `SKIPPED`, never `PASS`. |
| 3 | Required | Qualify the full CLI built by the exact phase 3 compiler and bind it to that producer, source, and runtime before interpreter execution. |

The phase's overall gate is incomplete while any required direct, BuildRunner,
or interpreter case is `UNRUN`, `UNSUPPORTED`, or `FAIL`. In particular, the
current driver cannot yet consume separately receipt-bound phase 3 full-CLI
evidence, so phase 3 interpreter qualification remains pending that integration.
Do not promote a direct-only matrix `PASS` to phase completion when required
BuildRunner cases remain `UNRUN`.
