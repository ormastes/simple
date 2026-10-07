# Item 5 app-source manifest v2

The item5 app receipt runner keeps Phase2 producer provenance distinct from
the source snapshot used to build each app binary. The manifest names the
Hello compiler SHA and producer source commit, plus an app source commit and
its Git tree object ID. The deterministic tree ID is
`git rev-parse <app_source_commit>^{tree}`. Each app entry repeats the same
app commit/tree pair and compiler SHA, and supplies its binary SHA-256.

The focused regression accepts different producer and app commits. It rejects
wrong compiler or producer bindings, mismatched per-app source commit/tree,
object IDs with a noncanonical 41-character length, and nonnumeric Hello exit
status. The runner preflight harness also consumes v2 manifests and still
rejects missing staged binaries before trying to execute them.

The manifest is caller-supplied provenance metadata, not independent proof of
how a binary was produced. The canonical Phase2 Hello gate still needs a
formal machine-readable PASS receipt for the runner's producer input. Retained
logs or a compiler hash are not converted into a synthetic receipt here. Until
that bridge exists, end-to-end app evidence cannot be admitted through this
runner. No Simple app binary was built or run for this change.
