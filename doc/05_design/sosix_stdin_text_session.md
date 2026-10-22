# Checked stdin text sessions

Source preparation for the selected `utf8_internal_sosix_plan.md`; execution is UNRUN.

`std.nogc_async_mut.sosix.stdin` supplies `sosix_stdin_text(codec)` and
`sosix_stdin_utf8(input_byte_limit)`. They bind existing descriptor zero through
`StdinTextSession`; no descriptor adoption API or external text value appears in
ordinary signatures. Configuration is immutable and admitted before reads.
UTF-8, UTF-16 and UTF-32 use the existing strict decoder with explicit endian and
BOM policies. No locale detection or replacement decoding is introduced.

`read_chunk(size)` returns `Some(text)` after positive encoded input, including
`Some("")` when a scalar/signature is incomplete; it returns `nil` only after a
zero-byte provider read and successful decoder finish. Short positive reads are
not EOF. `read_text(size)` skips pending empty chunks, consuming bytes on each
iteration. `read_scalar_text()` reads one encoded byte at a time and yields one
complete scalar as valid internal UTF-8 text; it deliberately does not expose a
primitive Char while physical Char integration remains pending. NUL is content.

Provider and codec errors become sticky and preserve their typed errors. Invalid
read sizes fail before I/O and are recoverable. `is_open` means not logically
closed or failed; EOF has a separate `at_eof` observation. Logical close is
idempotent cancellation: it neither calls close(fd0) nor validates unread input.
Ordinary references share the same state, but exclusivity/affinity/concurrent
serialization is not enforced. Users must serialize access to process-global
stdin and cannot safely reset a decoder in the middle of its encoded stream.

A positive per-read input limit is at most 16 MiB; this is not a total stream,
blocking-time, allocation or RSS guarantee. Decoder carry is at most three bytes.
UTF-16 output can expand relative to encoded input, and existing checked codec
allocation/provider boundaries remain prerequisites. Scalar reads deliberately
trade syscall count for avoiding read-ahead or a second pending output buffer.
No throughput or OOM qualification is claimed. No global cache is introduced.
The existing POSIX byte provider is required. Windows console/binary mode and PTY
behavior are unqualified, and other platforms return typed Unsupported before I/O.

The existing integration runner launches the actual native fixture through
`process_run_bounded` with a 10-second deadline and 4096-byte output limit. The
fixture path must be explicitly supplied as `SIMPLE_STDIN_SESSION_FIXTURE` from
an admitted native build; no bootstrap CLI or seed substitute is permitted.
Seventeen scenarios cover encoded scalar/BOM boundaries, NUL, malformed/truncated
input, EOF, preflight validation, provider failure and logical shared-reference
close. The parent launches one fixture per scenario; no persistent process or
artifact cleanup protocol is added. All scenarios and native execution are UNRUN.

This adds the checked API; existing unchecked stdin/read-line APIs are unchanged.
It does not complete process encoding sessions, physical Char, text indexing,
Windows console support or the full internal UTF-8 plan.
