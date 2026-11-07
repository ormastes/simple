# Finite Engine exec codec specification

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/engine_exec_codec_v3_spec.spl`.

Manual source mirror: seven authored cases, UNEXECUTED. JSON/wire fixtures assert pure codec branches, not an actual Engine session or transport outcome.

| Case | Oracle |
|---|---|
| Exact create | Independent full JSON and HTTP request preserve literal argv/env, false privilege/stream flags, numeric user and fixed parent route. Nonce is not injected. |
| Unsupported requests | Secret references, stdin/TTY, excessive control window, bad parent and unsafe/parent-equal exec IDs refuse. |
| Create response | Exact Id accepted; partial, duplicate, nested, wrong-type/key, foreign-shape and trailing bodies refuse. |
| Inspect correlation | Exact parent/process schema matches, command-only null tail accepted, wrong user/privilege/stream/PID/parent refused. False running/zero exit remains metadata. |
| Detached start | Exact pinned request and200 ASCII-LF response;204, empty or JSON-string body refused. |
| HTTP framing | Canonical finite response accepted; duplicate/injected/control/overflow/chunked/incomplete/trailing/wrong-status/type responses refuse. |
| Evidence domains | Socket policy changes query digest; actual wire differences change response evidence digest without pretending HTTP is a CLI command. |

Content-Length-only is a supported subset; chunked Engine responses are explicitly unsupported. Any refusal after uncertain create submission must be handled by a future owner-bearing unknown-create journal, never inferred to authorize retry. No such effect/journal is implemented here.
