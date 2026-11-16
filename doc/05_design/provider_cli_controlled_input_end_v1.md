# Controlled input-end boundary

Design-only; no native edits, exports, task invocations or claimed EOF producer.

Expanded source inspection distinguishes three actual owners. Adopted primary
input uses the live Input issuer and the terminal's canonical controlled native
handle. Finite owned-process V3 startup instead queues a fixed initial payload
and closes that different process lease's stdin after it drains; its
`input_receipt` does not control an adopted primary session. Existing
`local_unix_shutdown_write_v1` owns an actual LocalUnixConnectionV1 and cannot act
on a PrimaryAttach process reference or Windows named-pipe lease. Input revocation,
detachment, connection cleanup and workload settlement have different effects.

The inspected common tagged input/write, native gate/pipe facade, Linux process
owner, V5 issuer and owned-process startup code expose no current controlled EOF
operation for the adopted primary handle. This is a bounded source conclusion,
not proof of absence from all external providers.

## Candidate lifetime if an actual primitive becomes available

An explicit versioned end-input request must bind the current actual adopted
session/runtime generation, live Input lease/target/principal/nonce/revision,
explicit next attempt, current frame sequence, exact payload digest/length and
positively known completed prefix. The same canonical issuer must refuse while
any write is Queued/Unknown or an earlier suffix remains unaccounted. It reserves
the exact end request as Unknown before the native transition. No implicit frame
increment, resend, nonce rotation or guessed EOF follows a lost reply.

The native owner must recheck that same live input gate under its existing
revision/handle barrier and return an owner-correlated input-half-closed receipt.
It must preserve output/read ownership and distinguish rejected-before-effect,
pending, conclusively closed and unknown. Exact retries observe/reconcile the
reserved operation rather than close again. End-input must not signal, stop,
detach, reopen the engine, create another PTY, or release the workload's charge.
Native input closure still does not establish provider consumption or workload
completion; actual wait/control/settlement stays separate.

On Linux's current process-backed attach, the real retained input descriptor
would have to be closed by its actual process owner under that gate, with stdout
and exact helper lifetime preserved. A caller FD/PID cannot perform that action.
The finite-startup V3 auto-close path is not that producer.

On Windows's current duplex named-pipe primary, no generic write-half-shutdown
primitive was identified. Closing the entire pipe is transport cleanup and loses
the read side; it is not an accepted input-end receipt. An end-input profile must
remain unsupported until the actual installed Engine/transport supplies explicit
input closure semantics and retained cleanup/read evidence. No `CloseHandle`,
newline, control character, revocation or zero-length WriteFile is promoted to
that proof. Existing native function names are not permission to change their ABI.

No native extension is implemented or authorized by this proposal. Any future
producer needs its own exact ABI/version, owner/lifetime review and native fixture
qualification. Current stdin plans remain refused before task effects.

## Independent documented argument mode

The selected original plan permits stdin, private-file or documented argument
injection. A bounded explicit Codex Argv mode can use the verified positional
prompt and Clap `--` delimiter; it is not generic stdin/EOF support. Exact Codex
0.169.0 root prompt handling appends piped stdin and reads it to EOF, so a valid
noninteractive Argv task additionally needs actual pre-first-start closed stdin
and non-TTY evidence. Request `terminal_mode=none` DATA alone cannot supply it.
Mandatory actual Config.OpenStdin/Tty/StdinOnce projection and a versioned
restrictive Host check are being coordinated with the existing config owner.
Absent/nonboolean fields must refuse; existing config-V1 wire/digests stay intact.

Argument mode makes prompt bytes visible to process/container inspection and
retained signed operation metadata. It must be an explicit selected input mode,
bounded in UTF-8 bytes and total argv size, never a shell command string or a
silent fallback from unsupported stdin. Current pure/contained source freezes
remain unchanged until this new mode/profile is separately reviewed.
