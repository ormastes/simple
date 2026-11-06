# Source-view route

The authored `source_open` route defaults to a folded native Simple outline. Use `mode: focused` with an unambiguous `target` such as `Counter.second`, or `mode: raw` for exact undecorated source pages. Structural support is currently Simple-only; unsupported languages return an explicit refusal and can still be read in raw mode. L1 syntax is not semantic resolution or typechecking.

Inputs: workspace-relative `path`, `mode`, optional `target`, outline `depth` (1 or 2), `max_nodes` (1–64), `max_bytes` (1–8192, default 4096), `snapshot_id`, and structural `cursor` or raw `start_byte`. Continuations must keep returned snapshot and query settings. Changed content/query yields stale. Native outlines admit at most 64 KiB/512 nodes; raw files at most 1 MiB. Oversized indivisible syntax/lines require a larger budget within the limit or explicit raw inspection.

Structural results separate exact source segments from display labels, with byte ranges, absolute first lines, folds, noncontiguous import ranges, omissions, diagnostics and explicit partial context. Relevant import semantics and function-body analysis are not evaluated. Raw strings are JSON data; never strip display decorations to manufacture editable source.

MCP and authenticated Caret HTTP use the shared `app/source_view/service.spl` result contract. Ordinary MCP does not infer logical agent identity. The authenticated host supplies registry-validated session state; it owns first-help commit and workspace mapping. Bound line-number preferences affect display only. Inline info/hints remain explicitly unavailable.

No compiler or external process is launched by this route. Disk snapshots are not editor overlays, and the current bounded reread/reparse is not the planned shared cache. Ancestor checks are not an atomic hostile-race sandbox.

Deployment status: authored source on the release lane; no admitted pure-Simple runtime or real MCP lifecycle receipt yet. Do not advertise the installed binary as supporting these changes until rebuilt admission and protocol smoke pass. The full selected plan remains open; consult the admission record and provider-gap record before making completion claims.

Bound service calls carry the authenticated owner's explicit canonical `workspace_root`; they do not reread process cwd after authorization. The unbound local MCP path captures cwd once. Descriptor-relative protection against malicious directory replacement remains a separate open IO requirement.
