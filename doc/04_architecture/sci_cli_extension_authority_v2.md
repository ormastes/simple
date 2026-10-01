<!-- codex-design -->
# SCI CLI extension authority v2

## Decision

Keep section 10 (`CLI_OPTION_ROUTE`, v1) unchanged as the compact, immutable
route index. Add required section 11 (`CLI_EXTENSION_AUTHORITY`, v1) only when
section 10 contains extension-namespace routes. Section 11 is the canonical
serialized source of `SimpleCliExtensionV1`; it is not a host-side optional
table and it is never reconstructed from provider metadata.

This is wire v2 at the composition-image feature level, not a mutation of the
section-10 binary layout. Images with no section 10 remain v1-compatible.
An image with section 10 but absent, unknown, corrupt, non-canonical, or
section-10-digest-mismatched section 11 is rejected with a typed SCI diagnostic.

## Section 11 contract

The section has a fixed header, SHA-256 body digest, sorted namespace index,
and canonical records. Its header binds the exact SHA-256 of the admitted
section-10 bytes. Each record contains:

- namespace (unique, sorted, same grammar as section 10);
- provider ID and binding service ID;
- ordered option records: key, flag/value kind, ordered closed values, help;
- an exact section-10 route binding: namespace, provider ID, availability,
  missing policy, and one-based binding index.

Decode validates the outer directory digest, section-11 body digest, its
section-10 digest binding, ordering/uniqueness, option grammar, value grammar,
and equality of every route-binding field. It also validates section-10 index
sort order, uniqueness, reserved bytes, record spans, per-record checksums,
and canonical record fields before binary search relies on them. It creates
`SimpleCompositionImageV2(image_v1, route_owner, authority_view)`; V1 and its
public constructors remain unchanged.

`route_owner` is one opaque reference-owned object containing the section bytes
and parsed handle. It is never a `[u8]` field passed by value. The same applies
to the decoded authority view. No argv token reparses either section or copies
an O(R) section body. Failures are `SciExtensionDiagnosticV2(code, subject,
message)`, never collapsed to prefixed text.

## Execution contract

`simple_core_execute_v2` receives only the decoded composition image. For an
extension route it locates the same namespace in the decoded authority view;
absence is `CLI_EXTENSION_AUTHORITY_MISSING` before provider admission.

Before the first `--`, that `SimpleCliExtensionV1` alone validates and applies
every selected namespace token. The original argv is retained exactly for a
RUN dispatch, including repeated options and batch arguments. At `--`, all
remaining words are provider/program data and receive no host lifecycle parse.

One invocation may select one extension namespace; a second namespace, even
when it names the same provider, is `CLI_EXTENSION_MIXED_NAMESPACE`.

For an extension request, pre-terminator `--help` produces
`cli_extension_describe_v1` output and pre-terminator `--complete [prefix]`
produces `cli_extension_complete_v1` output; neither opens the provider. The
unambiguous spelling is `--complete=<prefix>` (bare `--complete` means empty
prefix); `--` is never a completion prefix. A
normal extension run performs validate/apply then provider `VALIDATE_ARGS` and
`RUN`. Regular non-extension commands retain existing provider help, complete,
validate, run, and error behavior unchanged.

## Complexity and ownership

Decode pays one O(section-10 + section-11) authenticated admission cost and
one reference-owned decoded authority allocation. Extension routing is O(log R) for section 10
plus O(log E) authority lookup; validating selected option tokens is O(T*O),
where T is selected pre-terminator token count and O is options in that one
extension. There are no O(R) argv copies, section extractions, body hashes, or
header parses on the hot route path.
