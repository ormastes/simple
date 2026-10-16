# Query native array-tail range lowering unavailable

Bug ID: query-native-array-tail-range-20261016.
Status: temporary source workaround; bug DB reconciliation pending qualified tool.
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
an empty tail. New cases remain UNCOMPILED/UNRUN pending owner review and cycle2.
Cycle1 evidence remains in E/query-boundary-native-cycle1/terminal-receipt.json.
After real engine repair, qualify the intended grammar with the actual producer
before restoring recovery source. No smaller-context object graft is authorized.
