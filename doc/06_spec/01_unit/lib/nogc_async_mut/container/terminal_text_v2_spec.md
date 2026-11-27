# Incremental terminal presentation text V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests, builds or native IO were
executed. Every authored case calls the actual
`container_terminal_text_feed_v2` implementation and checks presentation bytes,
newly delivered native-byte counts, retained prefixes or refusal errors.

Source: `src/lib/common/contracts/container/terminal_text_v2.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/terminal_text_v2_spec.spl`.

| Authored case | Intended assertion |
|---|---|
| Scalar across reads | A two-byte euro prefix emits nothing and completes on the next read without counting the retained bytes again |
| Supplementary scalar | Every internal split of a four-byte scalar retains the prefix and reconstructs the exact original UTF8 bytes |
| Scalar across chunks | Prefix carry also works between chunks within one feed call |
| Independent channels | stdout, stderr and tty retain separate prefixes and emit completed scalars in supplied chunk order |
| Invalid bytes and NUL | Malformed bytes render as U+FFFD through the shared decoder; embedded NUL is preserved; native bytes remain the original count |
| Impossible prefixes | An invalid overlong prefix is replaced immediately; a complete surrogate follows the shared decoder's scalar replacement policy |
| Retained EOF flush | Incomplete retained bytes flush one replacement per unconsumed byte, clear all channel carry and add zero native bytes |
| Final chunks and closure | EOF also flushes new partial chunks and rejects every feed after the finished state |
| Pending read | An empty nonEOF feed preserves carry without output or byte-count advance |
| Native-byte bound | 65536 bytes accept; an oversized chunk or aggregate turn refuses without changing the supplied state |
| Chunk count | 1024 empty chunks accept; 1025 refuse |
| Failed-turn state | An invalid stream after an otherwise valid chunk does not consume the caller's prefix; an exact retry completes it |
| Retained-state bound | More than three pending bytes on any channel refuses before decoding or marking finished |

Transport data remains binary. This adapter performs presentation decoding and
retains only incomplete valid scalar prefixes. It does not normalize NUL, merge
per-channel UTF8 state, or equate rendered replacement bytes with native byte
counts. The shared decoder replaces incomplete EOF input one byte at a time;
complete malformed scalars may use its larger consumed-byte count.

These pure source cases do not establish actual Windows transport, terminal
rendering, authenticated ownership, output acquisition, or native qualification.
