# Target 6 native SHA stream on runtime-built archive bytes (2026-09-29)

Status: focused correctness fix; bounded archive publication and production
time/RSS qualification remain open.

The reverted cold-publisher candidate hashed its first archive member as
`3af113f991b99b09a2a6deebe0c579fb86e3cd3f7166d4584bd59197234c31d2`
instead of receipt digest
`9f63f2e1edaf9e26d3742a826204a1375848dc984c759e6016fa91d6aa7bd77c`.
A no-stub Stage-2 native probe used the exact 92-byte action-member text and
copied bytes from `text.byte_at`. Both `sha256_text` and `sha256_u8_hex` of
those bytes matched the receipt. A single `Sha256StreamV1.update` call on the
runtime-built `[u8]` reproduced the bad digest. Seven-byte chunk updates
gave another wrong digest; feeding the same source via `update_byte` matched
the receipt. The prior native SHA stream spec passed 4/4 literal-array
vectors, leaving this runtime-built array case uncovered.

`sha256_stream_v1_update` now indexes `[u8]` with signed `i64` offsets, as the
working one-shot hasher does. A permanent external digest vector constructs
the action member at runtime and checks the one-shot, single-update, and
seven-byte chunk paths. No-stub Stage-2 native build compiled 39 units with
zero failures; execution passed all 5 examples with zero failures.

The publisher still copies each whole member into a byte array before UTF-8
validation and hashing. This change fixes the stream primitive but does not
yet lower publication RSS or prove a compile-time improvement. The next
publisher candidate should hash/validate byte ranges directly, preserve
exact manifest and semantic admission, and pass a paired native time/RSS
cohort before replacing the current path.

## Broader gate limits

The installed pure-Simple runtime passed `check-core-runtime-smoke.shs`.
The Stage-2 bootstrap tool does not implement the smoke script's `-c`
command, so it cannot substitute for that CLI gate. The repository MCP
native smoke stopped at the existing wrapper contract's raw-source launch
in `t32_mcp_server`, before MCP/LSP server round trips. An installed-runtime
`check src/lib` invocation was stopped after ten minutes while it was still
processing individual batches; it has no whole-tree verdict. A direct
installed-runtime check of this single SHA file failed to resolve its imported
helpers in isolation, while the current-source no-stub native entry closure
compiled and passed the focused test. Full compiler/lib/MCP/LSP checks and
production-path qualification remain open.
