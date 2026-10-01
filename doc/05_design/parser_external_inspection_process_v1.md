# Compiler inspection execution stage V1

Scope: a bounded compiler owner for the existing pinned inspection facade.
`ParserExternalInspectionProcessV1` retains a private `ProcessInspectionLeaseV1`
and the real frozen capture. It accepts borrowed executable and cwd pins, a tool
kind, and artifact bytes. No caller supplies argv, environment, digests, terminal
facts, process handles or admission receipts. The facade binds both pins and the
compiler computes SHA-256 from the actual stdin bytes.

Readobj requests JSON file headers, sections/data, symbols and expanded
relocations; objdump requests default raw-byte disassembly. Both read stdin.
The environment is exactly LANG=C and LC_ALL=C. There is no PATH, shell command,
response file, plugin option or inherited environment. Bounds are 16MiB input,
15MiB stdout, 1MiB stderr (the native combined 16MiB cap), 30s wall budget, 100ms TERM grace, 2s cleanup budget.
Stage 6A requires ProcessGroup retirement. The current V4 provider accepts only
LeaderOnly and rejects ProcessGroup at runtime_process_owned.c:3787. This stage
retains the required ProcessGroup policy and is therefore BLOCKED until the
provider implements real descendant retirement. It must not downgrade to LeaderOnly.

State: Idle -> Running -> Captured -> Acknowledged. Failures after lease creation
enter CleanupRequired. Cleanup cancels, collects and acknowledges the current
native frozen snapshot; pending/error results retain the lease for explicit
retry. Success capture remains retained until acknowledgement succeeds. A
failed process never exposes a capture. The class is single-use after start.
No native integer or fabricated terminal is exposed. Caller closes borrowed pins.

## Admission remains blocked

Pinned identity and successful execution do not authenticate an LLVM release,
dependency closure or version. Existing tool-owner start/join remain blocked.
The returned opaque frozen capture is process evidence only; this stage does
not mint `ParserExternalInspectionTokenV1` or populate boolean proof receipts.
Parsing and semantic coverage joining remain separate stages.

## Verification and limitations

Unit specs cover fixed argv and rejection of idle collect/ack/cleanup. Native
integration uses an actual pinned `/usr/bin/false` process and bounded progress,
checks failure cleanup and denial of capture, and closes both pins. Unsupported
providers fail this spec; there is no fabricated fallback or skip.

Source-matched runtime was not established: the available local release binary
is dated July 25, while this worktree uses September 28 origin/main. Executable
specs are added but NOT run, and this change is NOT verification PASS. Full
compiler/lib/MCP smoke gates remain required before release.

The facade can return an error after native start while decoding a malformed
wire response, without returning its native lease. The compiler cannot clean
up a ticket it never receives. That existing facade boundary requires separate
hardening; all errors after a lease is returned preserve it here.
