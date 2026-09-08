<!-- codex-design -->
# Parser external inspection tool owner V1

## Purpose

Own the compiler-side policy and lifetime of the two external parser
inspection tools (`readobj` and `objdump`). The owner retains the exact
canonical path, image digest, dependency-closure digest, version identity,
argv/environment policy digests, and generation. A generation remains live
while any tool lease is live.

This is not an executable-path lookup facility. PATH lookup, shell command
strings, plugins, response files, and open execution policies are rejected.

## Authority boundary

`ParserExternalInspectionToolPolicyV1` is a candidate policy record. Its
fields are not trusted merely because a compiler caller supplied them. The
future OS/loader admission owner must authenticate the image and dependency
closure and the runtime must return an opaque pinned-process receipt.

`parser_external_inspection_tool_owner_start_v1` is therefore an explicit
blocked port while the runtime admitted-process ABI is unavailable. It never
uses the existing V3 `execvp` path. The join function also always returns
`InspectionAuthorityBlocked`; caller-constructed terminal, digest, or capture
facts cannot create an inspection token.

## Lifecycle

1. Register one closed policy for each tool kind.
2. Acquire opaque leases; record the exact policy generation on each lease.
3. Start through the future runtime pinned-process port, with immutable input,
   canonical argv, allowlisted environment, and bounded output.
4. The runtime owner returns an opaque pinned capture receipt only after exact
   image, process identity, input, terminal, and capture facts are joined.
5. The inspection owner reruns the existing bounded codecs and terminal join on
   owner-retained bytes, then issues the inspection token.
6. Release leases before revoking a generation.

## Test coverage

`test/01_unit/compiler/driver/parser_external_inspection_tool_owner_v1_spec.spl`
proves identity retention, closed execution-policy validation, generation
drain before revoke, and fail-closed behavior while the runtime port is absent.
