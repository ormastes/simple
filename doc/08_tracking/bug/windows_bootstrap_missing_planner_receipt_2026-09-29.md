# Native bootstrap planner receipt failure

## Evidence

Release run 36501285141, job 109192601810, revision
96c901e0130d3dd4f6d2528e47532e040ff6ef7e built the Rust seed and native library,
then failed at 2026-09-29T00:40:16Z with exit 64 and
`bootstrap-policy-error: reason-receipt-required`. The workflow invoked a full
bootstrap without an admitted planner receipt.

Linux Cranelift job 109192601656 failed with the same error at
2026-09-29T00:22:16Z. Both use the same repaired branch. Linux LLVM retains
its full-CLI path; this repair does not reduce that lane to Stage 3.

## Repair

Windows and Linux Cranelift now build the receipt-free Stage 2 trust root, invokes the canonical
planner receipt producer against that exact parent, and resumes admitted
Stage 3. The receipt producer and verification guards remain authoritative.
The existing AOT workflow uses this same two-phase admission pattern.

The requested Windows/Linux concurrency uses 10 Cargo jobs and explicitly selects
--incremental-unlimited --jobs=10 for Stage 2. This opts these invocations out
of the default two-worker profile without changing the global default.
Stage 3 resume requires one thread by its current implementation; it rejects
other job counts. This change does not claim Stage 3 uses 10 threads.

## Validation and limits

Workflow YAML parsing, Bash syntax for both modified steps, working env guard,
and generated-spec layout passed locally. No Windows execution was available
for verification; the next CI run must qualify the receipt and native stages.
The failed runner was GitHub-hosted windows-2025-vs2026. Its log did not record
a processor count. Repository runner discovery found only Linux self-hosted
runners. Local Windows host profile DESKTOP-5A4V03J has no connection endpoint
or CPU inventory. Ten jobs therefore does not establish ten available cores.

No full bootstrap was restarted during this repair.

Resume artifact paths now follow the admitted host triple: Windows executables
use .exe, MSVC archives use .lib with no lib prefix, and GNU Windows archives
keep lib*.a. The workflow explicitly exports the MSVC ABI so Git Bash does not
select GNU for the receipt/resume subprocesses. Backend remains bound to the
admitted Stage 2 command transcript. Original Windows/Linux Cranelift used
--no-mcp and no --full-cli; bootstrap-from-scratch stops after Stage 3 in that
configuration, so the resumed flow retains the requested stage scope.

The planner producer and bound verifier derive planner.exe from an admitted
.exe parent, sharing one helper. Exact path pinning and argv digests still
use the same derived path; alternate executable names are not admitted.

The admission regression harness had a stale producer path and obsolete
positional subcommand; both are corrected. Its canonical positive admission
now passes producer and verifier. The configured-output fixture then fails:
the producer still requires the Stage 2 admission receipt beneath default
build/bootstrap although that fixture uses build/bootstrap-custom. Three
repair/verification cycles are exhausted; negative fixtures after this failure
remain unexecuted. Full admission regression PASS is not claimed.
