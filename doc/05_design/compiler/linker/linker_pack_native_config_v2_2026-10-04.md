# Native configuration transport V2

ITEM4-REQ-010 / positive provider prerequisite. Source/test design only; execution
and canonical manual generation UNRUN. Full provider/CLI/authority gates remain open.
Owner `/root/linker_research`, session `item4-pack-wire-spec-20261004`, branch
`work/item4-pack-wire-spec-20261004`, isolated worktree
`C:/dev/simple-item4-pack-wire-spec-20261004`, base/expected target `b0f0cf98787`.
Runtime agent owns production wire/command/pack source; root owns integration.

`LinkerPackJobV2` contains request, policy, inputs, output and
`native_config: NativeLinkConfig`. `linker_pack_encode_job_v2` and
`linker_pack_decode_job_v2` live in `linker_pack_config_wire.spl`. V1 is retained;
neither version decoder accepts the other's envelope. Command stays `linker-v1`.

| Position | Meaning |
|---|---|
| 0 | `simple-link-job-v2` |
| 1 | Canonical unsigned decimal count of complete V1 argv |
| 2 onward | That many V1 words, including `simple-link-job-v1` |
| c through c+3, c=2+count | runtime_path, target_triple, linker_abi, runtime_bundle |
| c+4 through c+10 | pie, debug, strip_output, prefer_size_linker, verbose, allow_duplicate_definitions, allow_cc_fallback |
| remaining | Four counted literal arrays: libraries, library_paths, retained_symbols, extra_flags |

Boolean words are exactly `0` or `1`. Counts reject sign, noncanonical leading
zeros, overflow, remaining-length mismatch and trailing arguments. Every string
rejects embedded NUL; empty native-config strings and array elements are preserved
because the wrapper owns their semantics. UTF-8 length, not character count,
determines the complete command arena cap: 28-byte request header + 9 command
bytes + 4-byte argument count + each 4-byte argument length and payload. Maximum
4096 arguments and 1,048,576 bytes applies to the whole V2 envelope. No claimed
count may trigger allocation before bounds checks. Encoder validates the same
contract; no truncating fallback to V1 is permitted.

The provider selects the version then calls `link_request_to_native_with_config`
for V2. V1 keeps historical default projection. Preserve actual engine identity,
target/host/policy receipt checks and independent lifecycle ownership. V2 is an
additive versioned argument protocol over the existing CLI command ABI; the V1
command ABI digest is not a promise that an older artifact accepts V2 argv.
Older providers reject the unknown job tag. Never retry as V1 and lose options.

The command regression uses an existing valid request with bounded policy:
incorrect explicit configuration target must yield InputError; correcting that
configuration must reach UnsupportedBudget. A default-projecting V2 handler would
fail the first expectation. This is real configuration-path evidence when run,
not a successful link, native mapping, whole-job budget or CLI completion claim.

Production callsite, explicit configuration dispatch and open authority/CLI/seal
work are owned by `linker_configured_dispatch.md`. This transport supplement
neither implements that integration nor supplies trusted manifest authority.
The six PACK-POS obligations remain separate from these six transport scenarios.
