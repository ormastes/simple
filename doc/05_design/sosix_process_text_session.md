# Explicit process text sessions

The synchronous SOSIX facade exports `sosix_process_text_session` and the
ordinary-text session/result/error types. ExternalFormat, encoded values,
decoders, raw handles and descriptor adoption remain inside the implementation.
The existing `OwnedProcessLease` V3 provider is unchanged. This API is native
Linux only; unsupported hosts are refused before process creation. No Windows,
PTY, interpreter-provider or affine ownership claim is made.

Three immutable TextSessionCodec profiles select stdin write encoding and
independent stdout/stderr read encodings. All metadata, finite limits, absolute
command/argv UTF-8 and NUL restrictions, and stdin encoding are admitted before
spawn. NUL is allowed in stream data. Each stdout/stderr decoder keeps at most
three carry bytes and validates BOM once at stream start. No locale inference
or primitive Char conversion occurs.

The common native capture limit is 1..1048576 encoded bytes per stream, fitting
both read profiles. Input is at most 1048576 internal UTF-8 bytes and at most
1048576 encoded bytes, additionally bounded by the stdin write profile. Command
and arguments total at most 1048576 bytes, with at most 256 arguments. Timeout
is 1..3600000 ms, grace 0..30000 ms; each poll waits 0..250 ms and requests
1..65536 bytes per stream. Conversion may allocate temporary input/output
arrays, and UTF-16 decoding can expand byte length. These are logical limits,
not total RSS, allocator-capacity or performance guarantees. There is no global
encoding cache and no accumulated session output string.

V3 delivery counters are per poll, whereas kept/seen counters are cumulative.
The wrapper tracks cumulative delivered bytes with checked bounds. Empty
output is pending/progress, not EOF. Decoder finish happens only after the
native terminal state and complete delivery of retained bytes for both streams.
Truncation and consuming codec/provider errors are sticky; no retained prefix
is presented as a complete successful text stream. Previously delivered chunks
cannot be retracted. Timeout and cancellation remain explicit lifecycle flags;
nonzero child exit remains result data.

Each successful start publishes one shared class owner holding the native lease.
The caller serializes aliases; copying a reference does not create a second
native owner. After an error, `cancel` and `collect` remain available. Collection
explicitly begins retirement and discards unread output. Each call performs one
bounded raw drain, then returns nil while native retirement is pending. It does
not retry automatically or erase ownership. Once native collection succeeds,
all aliases observe the closed state and reuse is refused. A collected result
retains native errors and does not assert successful decoding. Malformed native
receipt/ABI failures leave cleanup unqualified; they are never declared closed.
`input_receipt` preserves accepted versus written bytes, closure and native error;
acceptance is never treated as delivery.

Fourteen actual process API scenarios and one native fixture are authored.
All are UNRUN pending the qualified runner. They use real Linux child pipes,
ordered UTF-8 byte/NUL assertions, explicit LE/BE/BOM profiles, truncation,
timeout, cancellation and retirement. Fixtures have bounded turns; success-path
cleanup is explicit, while a test abort can still strand its child until provider
deadline/host cleanup. No test evidence or full UTF-8-plan completion is claimed.
