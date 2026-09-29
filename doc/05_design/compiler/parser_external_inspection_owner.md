# Admitted external parser inspection owner

Date: 2026-09-08. Selected configuration: registry B and atomic input 1.

## Current executable boundary

`parser_external_inspection_captures_v1.spl` supplies the normalization operation
the future live owner calls on its retained artifact and four captures. It
checks the V3 16 MiB input limit, both terminal input counts/digests, output
limits before decoding, every reported executable section's range and exact
input-byte digest, and non-overlap. It re-runs readobj section/relocation/group
decoders, objdump decoding, data coherence, exact-byte feature classification,
and terminal joins. It accepts no caller-decoded data or feature projection.

Its result is inert data. It neither authenticates an executable image nor
proves that arbitrary bytes form a complete valid object. Section completeness,
symbol/relocation fidelity, and tool identity require admitted process output.
The fixture tests are synthetic normalization tests, not external tool or native
execution evidence. The existing classifier also leaves legacy instructions
unclassified; its scalar projection cannot prove baseline legality.

## Missing authority prerequisite

The inspected native V3 start still reaches `execvp(cmd, argv)` in
`runtime_process_owned.c`; its public start contract has no explicit environment
array or admitted executable image. Even an absolute command path does not
freeze its contents, dynamic dependencies, version output, or inherited
environment. A safe RuntimeValue ABI adapter alone cannot close this gap.

Do not expose an inspection-token constructor over
`ParserInspectionToolTerminalV1`, digest strings, a PID, or a successful exit.
Do not add a shell/PATH runner as the implementation of this owner.

## Shared interfaces and ownership

These names are the proposed owner contract, not declarations for unavailable
native functions:

| Interface | Owner operation and retained state |
|---|---|
| `AdmittedInspectionToolBundleUseV1` | Runtime/tool owner issues a bounded use over exact immutable readobj and objdump executable images, version captures, dependency closure, fixed argument templates, codec versions, explicit deterministic environment, and generation. |
| `ParserExternalInspectionOwnerV1.inspect` | Consumes a live `BytesSealed` use, acquires the tool-bundle use, retains exact artifact bytes once, and starts two admitted-image V3 processes. No caller paths or precomputed digests enter this method. |
| `ParserExternalInspectionOwnerV1.poll` | Progresses both children with finite input/output quanta and bounded per-call/total bytes; cancellation is owner-recorded. Stores captures only in the owner. |
| `ParserExternalInspectionOwnerV1.finish` | Revalidates the live tool use, requires full input/closed stdin, untruncated output, exit zero, collected/reaped receipts for both tools, then runs the capture-normalization operation internally. |
| `ParserInspectionTokenV1` | Owner-issued opaque live token over an immutable retained normalization result plus the sealed-input and tool generation bindings. Has no public numeric constructor or field-based minting path. |
| `ParserExternalInspectionOwnerV1.acquire_use` | Pins a live inspection record for target/profile/build joins; returns a separate opaque use, not an authority-bearing projection copy. |
| `ParserExternalInspectionOwnerV1.release` | Revokes new uses, drains existing uses, releases tool and sealed-byte uses in reverse order, and retains cleanup-pending state when cleanup fails. |

The tool owner must provide an admitted-image spawn operation using a held
executable identity and explicit environment, with no search, response files,
plugins, caller working directory, or ambient-loader injection. For dynamically
linked tools, the executable inode alone is insufficient: the admitted closure
must include the loader and dependent libraries, or use an admitted isolated
tool image. Version checks run through the same image authority used for
inspection and are bounded separately. This is an implementation prerequisite,
not a claim that platform isolation already exists.

The public inspection projection additionally binds the input seal generation,
tool bundle generation, both executable/version digests, role-specific argv
digests, environment digest, codec and classifier identity, exact captured
output digests/counts, normalization digest, and completed cleanup facts. Those
fields are owner-derived and framed under a new inspection-owner digest domain.
Any replacement closes admission before issuing a new generation. Existing
uses can finish against their pinned old generation; new uses cannot revive it.

## Implementation and verification plan

1. Runtime lane completes the V3 opaque ABI adapter and its byte-array tests.
2. Runtime/tool lane supplies admitted-image execution and deterministic explicit
   environment. Freeze that API before writing the Simple owner; do not invent
   extern symbols with no implementation.
3. Compiler lane implements the owner and bounded token/use registry over that
   API, calling `parser_external_inspection_captures_v1` only on retained data.
4. Integration tests run both admitted LLVM tools against a real sealed object,
   compare all normalized sections/relocations/instructions, and reject changed
   input, swapped executable/version, changed argv/environment, output
   substitution, timeout, overflow, partial write, cancellation, stale/released
   tokens, and cleanup failures. A copied projection must fail as build authority.
5. Target/profile/cache joins consume a live inspection use inside their owner;
   actual SIMD execution and baseline legality remain separate acceptance gates.

Merge owner: root compiler/runtime coordinator. Final reviewer: Astra/highest
capability reviewer. The capture module and focused unit spec are implemented;
live inspection token issuance remains unimplemented pending step 2. Production
Simple execution remains subject to the existing self-hosted provenance gate.
## Existing executable-admission primitive

The hosted implementation should extend `rt_process_pin_executable` and
`rt_process_spawn_pinned_piped` rather than authorizing `execvp`. Those runtime
operations open an absolute regular executable with `O_NOFOLLOW`, copy it to a
sealed memfd, execute the exact fd with `fexecve`, and install a controlled
`LANG`/`LC_ALL`/`TZ` environment with a non-resolving `PATH`. Their static ELF
validator rejects `PT_INTERP` and `PT_DYNAMIC`; dynamic LLVM tools therefore
need a separately authenticated dependency-closure manifest or must fail
closed. SimpleOS should reuse the lifecycle semantics of
`executable_admission_pipeline.spl` and `executable_authority_registry.spl`.
