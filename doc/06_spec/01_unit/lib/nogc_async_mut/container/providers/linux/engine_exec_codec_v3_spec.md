# Finite Engine exec codec specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/engine_exec_codec_v3_spec.spl`.

Manual source mirror: eleven authored cases, UNEXECUTED. JSON/wire fixtures assert pure codec branches, not an actual Engine session or transport outcome.

| Case | Oracle |
|---|---|
| Exact create | Independent full JSON and HTTP request preserve literal argv/env, false privilege/stream flags, numeric user and fixed parent route. Nonce is not injected. |
| Unsupported requests | Secret references, stdin/TTY, excessive control window, bad parent and unsafe/parent-equal exec IDs refuse. |
| Create response | Exact Id accepted; partial, duplicate, nested, wrong-type/key, foreign-shape and trailing bodies refuse. |
| Inspect correlation | Exact parent/process schema matches, command-only null tail accepted, wrong user/privilege/stream/PID/parent refused. False running/zero exit remains metadata. |
| Detached start | Exact pinned request and200 ASCII-LF response;204, empty or JSON-string body refused. |
| HTTP framing | Canonical finite response accepted; duplicate/injected/control/overflow/chunked/incomplete/trailing/wrong-status/type responses refuse. |
| Evidence domains | Socket policy changes query digest; actual wire differences change response evidence digest without pretending HTTP is a CLI command. |
| Shared chunk decoder | Typed info request and chunked JSON decode use the same parser; start retains its distinct LF semantics. |
| Chunk bounds | Extensions/trailers/overflow/incomplete delimiters/trailing data, simultaneous CL/TE and excessive chunk count refuse. |
| Raw byte evidence | A UTF-8 scalar split across chunks reassembles and hashes successfully; equivalent Content-Length body has distinct wire evidence. |
| Same-response API | Info exposes exact5.2.5; missing, wrong or duplicate version header refuses without a separate ping. |

Finite Content-Length or bounded chunked encoding is supported; extensions and nonempty trailers remain unsupported. Any refusal after uncertain create submission must be handled by a future owner-bearing unknown-create journal, never inferred to authorize retry. No such effect/journal is implemented here.
