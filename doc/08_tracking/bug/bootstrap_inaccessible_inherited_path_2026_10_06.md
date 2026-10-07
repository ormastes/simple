# Bootstrap rejects an inaccessible incidental PATH directory

Phase1 source `52ecacbf27690be64cbeee4b59ec678baa5a4d0f`, attempt 1,
successfully materialized 61 links with zero failures, then exited at
`bootstrap-from-scratch.sh:1494`. The inherited PATH included a protected
WindowsApps PowerShell installation directory. Its existence test succeeded,
but directory traversal failed and `|| exit 1` aborted bootstrap before build.

An incidental inherited directory is not an admitted tool authority. The
canonicalization loop now reports and skips entries whose `cd`/`pwd -P`
operation fails. It still excludes missing directories and transient launcher
shims, preserves order, canonicalizes readable entries, removes duplicates,
and rejects an empty canonical PATH. Subsequent required-tool discovery,
toolchain selection and tool identity/provenance checks are unchanged. No
compiler fallback is introduced. If the skipped directory contained the only
usable required tool, later discovery still fails.

The active attempt 2 was not modified. Its independent environment workaround
removed only the protected directory after verifying cargo, rustc, clang-cl and
Windows PowerShell remained discoverable. The source repair is for later runs.

`scripts/check/check-bootstrap-path-access.py` executes the actual extracted
canonicalization block on ten independent cases: readable, missing, traversal
denied before/after readable entries, canonical duplicates, spaces, empty PATH,
only missing, only inaccessible, and launcher shim exclusion. A shell-local
`cd` fault injection targets an existing directory, avoiding elevated ACL
requirements. Other traversal uses the real shell builtin. It does not mutate
the caller PATH, run bootstrap, change ACLs, or launch a compiler. Cases continue
after individual failures. Full bootstrap qualification with this fix is UNRUN.
