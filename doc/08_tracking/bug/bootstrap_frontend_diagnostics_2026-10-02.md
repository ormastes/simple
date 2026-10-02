# Bootstrap frontend diagnostic cluster, 2026-10-02

Status: candidate fixes; executable and native validation UNRUN. This is not a
verify PASS or authority to deploy a rebuilt compiler.

## Recorded evidence and scope

The immutable catalog `D:/dev/bootstrap-failure-catalog-20261002/failures.json`
records overlapping attempts, not a count of unique bugs. This lane starts from
release commit `0d722af3d6` in its own worktree; frozen bootstrap source trees and
other agents' worktrees are unchanged.

| Group | Attempts | Source finding and candidate change |
| --- | --- | --- |
| missing_cli_export | F0004 | The package facade selected for `std.nogc_sync_mut.cli` does not provide `get_cli_args`; import its existing `cli_util` leaf owner directly. |
| parse_failure | F0032, F0055 | Startup binding lines 70 and 100 put the annotation on an indented line after `:`. Module binding parsers immediately expected a type token. Consume and balance that continuation's indentation for `var`, `val`, and lazy `val`. |
| hir_type_resolution | F0033, F0034, F0056, F0057 | Fully dotted `EnvironmentDigest256V1` annotations reach HIR as named types but were looked up as bare symbols. Resolve the exact module surface, register only the qualified member, and preserve the terminal type representation. |
| invalid_export_origin | F0065 | Unresolved terminal origins from `compiler.frontend.core.__init__` are recorded while lowering `lexer_types`. Current release already has canonical-origin alias lookup plus retained scalar alias fallback. The terminal's presence in the failed producer registry has not been established. No speculative change or suppression of this error. |

The catalog producer is
`e7ec89c1f106353cc8fdc792d5d41359336c72287f410aa039b57d8f6101dfdf`.
Windows owner confirms its `stage2-fixed.exe` supports baseline native-build but
not `run`, and cannot verify changes to its own compiled frontend without a
source-consistent rebuild. The recorded source commit is unavailable in the
isolated repository's object graph; no producer/source freshness claim is made.

## Acceptance checks and regression design

- `declaration_annotation_continuation_spec.spl`: array and optional annotations,
  subsequent declarations, immutable/lazy parity, and malformed continuations.
- `qualified_named_type_spec.spl`: std-to-lib owner aliases, a competing local
  type, existing local namespace bindings, primitive/nominal alias
  representation, absent owners/members, repeated lookup.
- Re-run the exact failing loader entry closures on a newly rebuilt producer;
  preserve logs and producer/source identities. Type resolution success must
  not be inferred from a different downstream failure alone.
- Re-run F0065 with registry evidence showing the terminal owner and physical
  surface index before changing export-origin validation.

The implementation uses existing indexed surface resolution and qualified type
bindings. A repeated resolved type returns its existing ID. It introduces no
filesystem/environment/process access, registry scan, or host-specific path.
Host interactions remain outside these frontend changes; no new SOSIX boundary
is introduced.

## Validation and remaining work

Source review and whitespace audit are separate from executable validation.
Peer review identified two candidate regressions before publication: dotted
namespace aliases needed their existing exact symbol lookup preserved, and
nominal aliases needed an owner-qualified binding for the alias spelling. Both
were corrected and have behavioral regression cases.
No native build slot was allocated while the manager and host owners were using
the guarded capacity. Parser/HIR behavioral specs, native fixtures, required
compiler/lib/MCP checks, runtime smoke, and performance validation are UNRUN.
F0065 remains open. The draft is reviewable work, not evidence that all recorded
bootstrap failures are fixed.
