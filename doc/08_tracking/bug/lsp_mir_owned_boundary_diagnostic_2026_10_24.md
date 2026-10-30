# Distinguish the LSP MIR owned-boundary refusals

The canonical Stage 2 LSP build from compiler `30a793...335` failed before
qualification at `mir_archive_try_production_repository_v1`. Its diagnostic
combined two conditions: a nonzero transient scope state, or nonempty cached
HIR warnings. The retained cache has 58 entries, including 17 warning-bearing
entries, but its hash-only filenames and retained receipts do not identify the
last module's key. Those counts do not prove which refusal condition occurred.

The diagnostic-only change separates the existing refusals and includes their
scalar state/count. It preserves short-circuit order, the original diagnostic
prefix, and strict ownership policy. It never clears warnings or admits a
lookup previously refused. No exact-message test required adjustment in the
bounded source audit. The next identity-bound LSP run must provide the missing
branch evidence; LSP qualification remains failed/pending, not fixed.
