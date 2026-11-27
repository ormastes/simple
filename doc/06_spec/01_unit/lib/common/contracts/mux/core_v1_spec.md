# CoreMux discovery value validation

Source: test/01_unit/lib/common/contracts/mux/core_v1_spec.spl.
Requirement links: REQ-CMUX-006 and REQ-CMUX-008.
Status: **NOT_RUN**. This is an authored manual mirror, not generated execution
evidence. Phase3 admission and a matching full test CLI are prerequisites; no
seed or Phase2 fallback is allowed. Docgen and spec-maintain are pending.

The unit controls call the production pure validators. They construct value
records, never fake a backend, launch a server or certify a lease. Accepted
representation is not proof of live ownership, support or a qualified receipt.

| Cases | Expected result |
|---|---|
| Unicode namespace, exact ASCII and astral UTF8 byte boundaries | Preserve text; reject one byte/scalar beyond the byte budget |
| Empty/control/NUL/path namespaces | InvalidRequest, NotApplied, no receipt/revision or affected objects |
| Both backends and endpoint policies, Unicode client identity | Preserve explicit selection; perform no connection |
| Empty/oversized client identity; zero/negative/excessive limits | Reject malformed request values |
| Incarnation and lease token; zero generation/malformed token | Preserve valid opaque values; reject invalid shape without claiming authority |
| Every object kind; invalid owner/generation/object ID | Preserve typed references or reject invalid representation |
| Empty and multi-session snapshots, Unicode names | Preserve ordered actual field values and configuration revision |
| Duplicate session IDs | Reject and leave the original input unchanged |
| Duplicate names with distinct IDs | Retain ambiguity; live target resolution remains provider work |
| Cross-owner, stale-generation or wrong-kind session entry | Reject inconsistent metadata |
| Invalid session names and oversized collections | Enforce bounded metadata |
| Unavailable plus NotRun; Blocked with reason | Keep support and execution evidence separate |
| Missing Blocked reason or Qualified receipt reference | Reject incomplete evidence representation |
| Capability backend/owner/generation mismatch or duplicate operation | Reject inconsistent descriptors |
| Session count beyond advertised limits | Reject inconsistent discovery snapshot |
| Exact 256-session bound and unique identity values | Preserve all entries, including the final ID |
| Capability owner/generation/version/limits and constraint boundaries | Reject malformed descriptors and excessive counts/text |
| Qualified reference text and oversized evidence | Preserve reference as unverified data; reject excessive text |
| More descriptors than discovery operation variants | Reject the oversized descriptor set |
| C1 scalars U+0080/U+0085/U+009F inside namespace/client/session names | Reject validated UTF8 containing controls |
| U+00A0, U+0100, Hangul and astral scalars | Preserve valid Unicode; continuation bytes alone are not controls |
| Windows drive-relative/absolute paths and trailing dot/space aliases | Reject; preserve existing Caret namespace labels and internal dots |

There are 33 authored cases. Loops exercise multiple concrete boundary values;
actual executed case/assertion counts must come from the admitted test runner.
No claim is made for branch coverage, host effects, control-mode framing,
Unsupported operation side effects, real tmux/smux compatibility or N2 soak.
Those require the connected provider and separate system/native qualification.
