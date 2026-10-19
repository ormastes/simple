# File text routing on the current base

Status: source port, execution **UNRUN**. This is the file slice of the selected UTF8/SOSIX plan, not full host migration.

| Surface | Routing and retained contract |
|---|---|
| File.read/write/append/open_text | FileTextSession with explicit codec; ordinary UTF8 Preserve; convenience output encoded before truncating open |
| FileHandle text/line methods | Shared strict codec and bounded accumulator; owning consuming read and transport-write failures close; raw bytes remain binary |
| io_runtime Result/nullable/exact/general/append/ranged text | Existing return shapes; strict validation before writes; existing parent-directory retry retained only on general write |
| file_ops replacement/positional/append | Original unlink/create, write-only 0644/umask, partial-count and empty-append behavior after strict admission |
| file_ops no-follow/mmap/atomic/exclusive | Preserve authoritative byte/no-follow or atomic/exclusive provider; strict UTF8 conversion |
| external_file/bounded_bytes | Explicit compatibility byte paths; scoped foreign windows; existing typed errors, no ordinary external-wrapper API |

No Unicode decoder is duplicated. Session format metadata stays private. Source rejects unknown/inconsistent metadata before opening; convenience output conversion precedes destructive open. Explicit FileTextSession.open(WriteOnly) still truncates. Limits are per operation, not lifetime totals. Nonzero positions preserve interior U+FEFF; UTF16 odd offsets fail. Append Require is refused before open; other policies inspect actual descriptor EOF. Concurrent appenders must cooperate on framing because EOF validation and write are not atomic.

## Ownership and copy behavior

FileTextSession is a class, not an affine value. Current MIR class_type_names metadata and function_lowering.spl retain class parameter reference identity instead of defensive struct copies. One shared instance therefore carries descriptor/config/mode/open state; the real alias-close/replacement-session test is UNRUN and remains required before claiming the compiler honors this. Private fields, automatic destruction and thread-safe sharing are not claimed. No raw adoption constructor or global registry is added.

Session/FileHandle close invalidate state before the native call. Convenience operations close on every post-open result path; primary operation errors take precedence. Encoding/range rejection before I/O leaves an existing session usable. Consuming reads, transport writes and failed positioned seeks close the owner; partial effects are not rolled back. Borrowed reads never close their descriptor. Foreign buffers are released before status branches and positional owners close their own descriptor on every result path. @unsafe annotations alone enforce none of these lifetime properties.

## Memory and evidence

The accumulator grows geometrically within a logical cap of at most 16 MiB; reads may consume one overflow probe byte. Old/new buffers, chunks, defensive copies, codec output and final Text can coexist. foreign_bytes caps one foreign window at 1 MiB; explicit external_file accumulation remains caller-sized and generic-array-backed. Neither static [u8] nor the logical limit establishes provider identity, OOM/refcounts, total heap safety or RSS.

Ordinary line reads use one-byte provider calls to preserve the next raw read's cursor. This creates per-byte managed-array/syscall cost. io_runtime.file_read_nullable now validates via the session route instead of its previous one-call path. These source-visible costs are tracked as OPEN, not presented as measured performance. No hidden read-ahead buffer or new cache is introduced.

The semantic port preserves unrelated io_runtime argv/cwd and all network/process/env/compiler/runtime owners. Landed sffi/fs writer ABI, TextSessionCodec, external_text_io and foundation sources are unchanged. The landed pure facade/config prerequisite specs are not overwritten by the historical mixed transport suite; file cases are isolated.

Source review cannot prove native class/Result dispatch, alias/private enforcement, seek/close/OOM fault paths, real partial writes, performance or platform behavior. The 35 actual-file cases remain UNRUN; root owns global attempt accounting.
