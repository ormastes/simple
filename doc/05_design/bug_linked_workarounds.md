<!-- codex-design -->
# Bug-linked workaround detail design

Canonical annotation: `# @workaround bug=<id> [recover=<hex>] [reason=<text>]`.
`//` is also accepted. The comment immediately precedes the affected block.
Bug ID is required; recovery reference is 7–64 hexadecimal characters; reason
is optional and recommended. Parser diagnostics identify source path and line.

The derived `.simple/workarounds.sdn` retains bug ID, path, source line,
recovery reference, and reason, with schema/revision metadata for validation.
It does not copy mutable bug status. A bug-check join classifies linked open
bugs as information and fixed/closed bugs as recovery-review warnings.
An optional `--bug=<id>` narrows the linked workaround view.

Incremental maintenance collects changed/untracked candidates plus previously
linked paths, so deletion and reversion of an annotation remove stale links.
For each supplied path, replace that path's records from its current contents;
absence removes its records. Preserve records for other paths. Reconcile all
tracked candidates only on explicit fullscan. A missing index or HEAD mismatch
reports that fullscan is required before claiming current coverage.

Mutation sequence: discover candidates once; acquire index writer lock; reload;
check schema/revision; parse and validate the complete batch; serialize; atomic
publish; unlock. A failed batch never publishes partial replacement state.
The query path performs no repair or content validation of source files.

Recovery sequence: fix and verify bug owner; list indexed links; compare the
optional Git reference to current source; apply a narrow reviewed restoration;
remove obsolete annotation; refresh on the next build; rebuild affected scope.
No automatic `git checkout`/`restore` is offered. A final clean qualification
occurs only at the existing bootstrap verification boundary.
