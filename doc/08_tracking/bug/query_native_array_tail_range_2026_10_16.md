# Query native array-tail range lowering unavailable

Bug ID: query-native-array-tail-range-20261016.
Status: temporary source workaround verified by the native query control;
bug DB reconciliation pending a qualified tool.
Recovery source:5e9123a377ef9a6278ec1ae6e65954112b84a4de.

First native query control build with producer0CD6 and that frozen source
completed72MIR modules:70successful,2failed,0objects, no link or control run.
Three errors reject a[start..] array tail ranges: query_commands.spl662/664
use parts[2..].join("/") and parts[1..].join("/"), and
symbol_resolution.spl152 uses slash_parts[1..].join("/"). Diagnostic:
unsupported range index a[start..end] / a[start..]; lower_range has no native
lowering. This is not the supported text-colon slice case.

Workaround: a typed lower-leaf scalar-text join helper iterates from the guarded
start, inserts a slash before each element after the first, and preserves empty
elements and trailing separators. Existing guards establish start2<len for
compiler peers and start1<len for other peers and owner-domain module paths.
It does not replace array ranges elsewhere or claim an engine fix. All changed
sites and the helper carry immediate workaround/recovery annotations.

The standalone native control now checks the real peer_path_tail API for
compiler/noncompiler path prefixes, internal empty segments, trailing slash and
an empty tail. These cases passed in the final native control described below.
Cycle1 evidence remains in E/query-boundary-native-cycle1/terminal-receipt.json.
After real engine repair, qualify the intended grammar with the actual producer
before restoring recovery source. No smaller-context object graft is authorized.

## Final scoped qualification

Workaround commit: `2081277b2fe12fc39057519313d5f16c9ce57a78`.
Qualified code source: `3a3e5628c3cbe31d317ef299b0fc7f2fb666dbc5`.
Producer SHA256:
`0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b`.
Candidate SHA256:
`587c774f14d0c297e6f76b43c0e5a82b4c00c94cc9fdbb1cbba70a15defb1cc0`.
The first native control execution passed with exit0, empty stderr and stable
hash, including real compiler/noncompiler peer-path tail cases with internal
empty segments, trailing separators and empty tails. Linking used a standard
lazy archive of all56 byte-identical SPL objects plus the canonical8-init entry
and38 current-source C runtime objects; no FORCE, ignored unresolveds, stubs or
SPL object grafts. See the sibling boundary-header report's evidence directory.
This qualifies the scoped workaround, not array range engine support, full CLI
capabilities, compiler generation admission or deployment. DB reconciliation
remains pending; the original grammar still needs a future engine repair.
