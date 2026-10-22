# File text sessions

Ordinary file text APIs return internal UTF-8 `text` and accept `text` on
output. Applications do not carry `ExternalText` or call a transcoder. Raw
byte methods still return/write bytes without text validation.

`File.read`, `File.write`, `File.append`, the ordinary runtime text facades,
and `FileHandle.read_text`/`read_line`/`write_text` use an explicit UTF-8 Preserve profile.
Their default whole-text input/output budget is 16 MiB. The existing error
shapes remain `IoError`, text errors, bool, or nullable text as appropriate.
An oversized text operation now fails; binary APIs retain their old limits.

For another encoding, construct one `TextSessionCodec` through
`std.nogc_sync_mut.io.text_session.text_session_codec` and open one file:

```simple:skip
val codec = text_session_codec(
    Encoding.Utf16, ByteOrder.BigEndian, BomPolicy.Require,
    Encoding.Utf16, ByteOrder.BigEndian, BomPolicy.Require,
    1048576, 1048576)?
var session = File.open_text("message.txt", FileMode.ReadOnly, codec)?
val content: text = session.read()?
session.close()?
```

`FileTextSession` is the only file session type. Each class instance owns one
descriptor and immutable read/write codec settings. Aliases share this state;
no compiler-enforced affinity or concurrent access safety is claimed. `open(path, mode, codec)`
has the same open/create/truncate policy as `FileHandle.open`; it validates
the codec before opening. A `WriteOnly` open itself truncates, as its name and
mode contract imply. `File.write` validates and encodes before that open.
Callers must close successful sessions; no automatic destructor is promised.

`read()` reads the remaining file within the input bound and returns decoded
internal text. It handles short native reads and byte sequences split across
8192-byte provider chunks. Empty input is valid with Preserve/Forbid; Require
at byte zero requires the declared signature. A decoding, allocation, or I/O
failure after a read closes the session. Input over the bound consumes at most
one overflow probe byte and is terminal. No malformed suffix can be retried
as a fresh message through that session. The owning compatibility method
`FileHandle.read_text` and `read_line` also close on a failed consuming text read; the raw
borrowed byte helper never adopts or closes its caller's descriptor.

`write(text)` encodes using the stored output profile and writes all encoded
bytes. Encoding or limit refusal occurs before writing and leaves the session
open. Transport failure closes it; a prefix may already have been written.
No rollback or atomic write is promised. `close()` marks the owner closed even
if the native close fails and is idempotent thereafter.

BOM policy applies at byte zero. Later reads/writes preserve U+FEFF as content
and do not emit a second required signature. `read_at(offset, size)` and
`write_at(offset, text)` use byte positions on this same descriptor. UTF-16
positions must be code-unit aligned; supplied frames must contain whole
scalars, and a truncated surrogate/UTF-8 sequence is an error. Successful
positioned operations leave the cursor after their transferred bytes.
Failed positioned seeks close the owner. `write_at` refuses Append mode. Required-BOM Append is refused before opening:
the existing append provider cannot atomically prove first-writer ownership.
Other append policies require actual opened-descriptor EOF and reject an
unavailable position or odd UTF-16 position. Cooperating appenders must preserve
code-unit framing; EOF inspection and O_APPEND are not one atomic transaction.
Preserve append remains available. No byte-order autodetection, normalization,
linguistic collation, encoding cache, or replacement decoding is provided.

The session reader allocates packed byte storage starting at at most 8192
bytes (256 for line reads) and grows geometrically up to the configured limit.
Whole-read chunks are at most 8192 bytes. Line reads use one-byte calls to avoid
stealing the next raw read's cursor, with per-byte syscall/managed-array cost.
Old/new storage, chunks, external copies, codec output and final Text may coexist.
The logical 16 MiB cap is not a 16 MiB RSS cap; physical cleanup and total resident
memory remain unqualified. Output
prechecks internal byte length against twice the output bound before full
conversion, then checks the exact encoded length. These are source bounds;
runtime RSS and latency remain unmeasured.

The low-level explicit external transport APIs moved from ordinary
`io_runtime`/`file_ops` and FileHandle methods to implementation owners
`io.file_external_compat` and `io.external_file`. They are retained for codec
and transport integration, not re-exported by the ordinary file facade.
Atomic/exclusive providers still admit UTF-8 only. Their low-level explicit
adapters retain typed refusal for UTF-16 and their existing durability and
permission semantics. Legacy replacement `file_write` still unlinks/creates
with the original 0644 provider; positional and empty append semantics remain
on their original providers. No file mode or raw byte provider was changed.

Validation: 20 actual-file session scenarios, 4 nullable-handle cases and
11 file-only compatibility cases are authored. The manuals mirror
their executable bodies under `doc/06_spec/02_integration/io/`. All are UNRUN
until root admits a qualified compiler/runtime. Source review cannot establish
native ABI, compiled dispatch, memory performance, or runtime success.

Current-base corrections invalidate FileHandle.fd before close, close failed
ordinary text writes, and close one-shot binary descriptors on operation errors.
The primary read/write error wins over close failure. Raw borrowed reads never
adopt/close their descriptor. External positional helpers release foreign
buffers before branching and close every descriptor they open.

@unsafe marks foreign-call preconditions; it does not enforce pointer affinity,
class aliasing, or concurrency isolation. Current MIR retains class reference
identity, but the actual alias-close scenario is UNRUN. No automatic destructor,
new resource adoption constructor, or global handle registry is added.

Explicit external-file helpers can accumulate their requested total in generic
array storage despite 1 MiB foreign windows. Ordinary positional text callers
apply their own 16 MiB cap. A [u8] type alone does not prove packed backing.
See doc/08_tracking/bug/file_text_session_provider_and_performance_20261019.md
for the unresolved provider, hot compiler read and long-line performance gates.
