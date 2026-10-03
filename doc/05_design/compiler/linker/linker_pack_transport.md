# Linker pack transport and ownership

Date: 2026-10-03. ITEM4-REQ-010 / G5 implementation slice; full gate remains open.

`linker_pack_entry.spl` exports the existing SimpleProviderQueryV1 and
SimpleCliCommandV1 scalar/arena ABI. `linker_pack_command.spl` decodes the named
`linker-v1` command and calls the production native request adapter. There is no
function-pointer reinterpretation or new runtime extern.

The job argv payload is `simple-link-job-v1`, 51 unsigned decimal scalars, output
path, input count, then counted paths. Headers use eleven words; targets six;
digests four. Request occupies words 0..33 and policy 34..50. Canonical decimal
parsing rejects signs, leading zeroes, overflow and narrowing. The command arena
is at most 1 MiB and 4096 arguments. Paths remain literal argv, never shell text.

The receipt is `simple-link-receipt-v1`, 28 scalar lines, engine, accounting and
outcome. It is at most 4096 bytes. Newlines/NUL cannot enter engine identity.
Policy identity hashes UTF-8 `simple-link-policy-v1` plus each of its 17 words
prefixed by LF, with no trailing LF. SHA-256 is stored as four big-endian u64s.
All policy values, not merely the schema digest, bind admission and the response.

Interface ABI digest is SHA-256 of the exact UTF-8 contract string:
`Simple linker pack v1: SimpleCliCommandV1 linker-v1; job-v1 51 u64 argv words; receipt-v1 28 u64 words; max command arena 1048576 bytes`.
Result: `f0d207492d516366fbc3a6e609a971f7812d1c17ac833a104d8f8d05ef0e3684`.
This local contract is not a claim of registration in the schema generator.

`LinkerLifecycleV1.publish_pack` validates its independent schema requirement,
then retains the loader's explicit owned query transition. Active generations
change only after successful native admission. Failed loads retain at most one
cleanup owner. Existing sessions pin old generations. Collection checks retired
state and pin count, unloads, then frees the slot; failed unload never frees it.
Static recovery remains independent of pack and session capacity.

Invocation validates independent request/policy/receipt schemas and exact host,
target, expected engine and policy identity. No cold hash/read/query occurs on
the hot call path. Bounded mode, strict enforcement, nonzero job-memory or scratch
limits reject before invocation until a parent-owned enforcing worker exists.
Provider assertions cannot establish QualifiedJobScope accounting.

Remaining G5 gates: registered production composition/seal and CLI selection,
dependency-closure/signature and hostile-path snapshot admission, successful
native-link corpus through the mapped provider, host recovery qualification,
latency/RSS/coverage and executed manuals. The generic loader's before/after path
hash is not proof of immutable mapped bytes or dependency identity. All current
tests are UNRUN; source review cannot certify these gates.
