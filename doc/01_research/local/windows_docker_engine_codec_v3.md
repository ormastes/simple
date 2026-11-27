# Windows Docker Engine codec v3 local audit

2026-11-07. Scope: pure protocol source only; **NOT_RUN**. No compiler, test,
Docker connection, Windows call, native broker or process was executed.

Reuse selected:

- `src/lib/common/json/value.spl`: typed JsonValue, decoded duplicate-key
  rejection through json_parse_value_strict, object builders and serializer.
  A codec lexical preflight bounds depth/tokens. The common unescaper replaces
  lone UTF16 surrogates; the codec rejects those before parsing identity/argv.
- `src/lib/common/net/http_core.spl`: body_decision rejects ambiguous/duplicate
  Content-Length/Transfer-Encoding; header_field_name_is_token and
  hex_chunk_size supply the shared lexical rules. The Docker profile bounds
  decimal/hex widths before numeric conversion and scans chunk payload as bytes.
- `std.common.text_bytes`: checked text extraction, strict UTF8 and byte/text
  conversion. Binary stream/framing bytes never pass through a text decoder.
- Existing Windows policy/request validators, semantic digest, scope fence and
  label projection helpers. Full independent JSON binding compares installed
  engine/policy and retained container request/scope before broker effects.

The old `std.nogc_sync_mut.http.response.parse_response` wrapper supplies an
HTTP200 default on empty/malformed responses. It cannot qualify private Engine
responses, so the new narrow codec does not call it. This is a boundary choice,
not a change to the general HTTP implementation. No general HTTP framework or
new native binding was added.

New source is `src/lib/nogc_async_mut/container/providers/windows/docker_engine_codec_v3.spl`.
It builds explicit Engine API1.48 request DTOs, decodes bounded strict control
JSON/HTTP, preserves hijack leftovers, and incrementally decodes Docker binary
multiplexed output. It does not open the pipe, admit an effect, persist an exec
birth, retry an unknown result, authorize input, own a process or release scope.

Integration boundaries remain explicit. Native broker must independently bind
full installed policy and retained request/scope, perform admitted create/start
writes under the live deadline, and persist actual exec-ID birth before start.
The v4 request extension now explicitly binds terminal_tty/stdin_open and the
actual create flags. Full codec binding derives TTY from that retained request
and checks actual OpenStdin/StdinOnce/AttachStdin; caller stream intent cannot
override them. Exec TTY remains independent. No host ConPTY output is
container-terminal evidence. The v4 request contract must land before this codec.

An initial concern that empty CLI argv necessarily inherited image CMD was
withdrawn: official Docker CLI docs state that --entrypoint clears image CMD.
No existing create builder was changed on that assumption. Exact actual
Entrypoint/Cmd checks remain useful; any Windows ArgsEscaped mismatch needs real
evidence before being called a defect.
