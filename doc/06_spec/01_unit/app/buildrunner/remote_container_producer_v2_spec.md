# Container producer argument grammar V2

Status: **AWAITING_VERIFICATION / NOT_RUN** — source-authored manual. No
compiler, seed, unit suite, process, provider or container was executed.

Source: `test/01_unit/app/buildrunner/remote_container_producer_v2_spec.spl`.
Implementation: `src/app/buildrunner/remote_container_producer_v2.spl`.

The pure grammar specifications create structurally valid `BuildTaskV1` values
with pinned source, compiler, runtime and nonce inputs, a declared compiler
output and the required probe receipt output. They call only
`remote_container_build_args_v2`, never the producer execution entrypoint.
Validation requires `native-build`, explicit relative pinned `--source` roots,
an exact pinned `--entry`, a declared `--output`, an allowed explicit backend
and `--entry-closure`. Optional `--strip` and multiple pinned source roots are
permitted. No default compiler, root, entry or backend is inferred.

| Scenario | Intended pure assertion |
| --- | --- |
| Explicit complete build | LLVM, LLVM library and Cranelift backend spellings accept with every required argument supplied. |
| Ordering and roots | Reordered flags, multiple pinned roots and optional strip accept. |
| Command and framing | Another command, positional shorthand, empty/incomplete argv and missing values reject. |
| Forbidden selection | Unknown cache, resume, seed, compiler, bootstrap, runtime and joined-value options reject. |
| Missing requirements | Omitting any required source/entry/output/backend/closure rejects instead of using discovery. |
| Uniqueness | Unsupported or duplicate backend, duplicate entry and duplicate output reject. |
| Portable paths | Absolute, drive-qualified, parent traversal, wildcard, backslash, empty-segment and newline-bearing paths reject. |
| Pins and output membership | Unpinned entry, false source-root prefix, using a file as a source root and undeclared output reject. |

Source review confirms that the actual producer requires its owned cwd and
declared probe output, completes same-process nonce-bound workspace preflight,
exclusively writes and reads back the receipt, and then starts test/build work.
The build branch selects the fixed pinned `tools/simple`, requires runtime
inventory under `tools/runtime`, sets explicit compiler/runtime/library paths,
disables stub/bootstrap delegation and rechecks all worker inputs afterward.
Its inherited-stdio compiler child remains inside the existing container; this
entrypoint does not launch another container. These are reviewed source paths,
not executed acceptance evidence.

No P0/P1 issue was identified in that reviewed ordering/selection under its
protected, serialized workspace contract. The workspace receipt and engine
selected-user observation are separate evidence; no UID/SID or ACL identity is
invented from environment variables. Actual filesystem preflight, compilation,
test execution, selected-user access and provider qualification remain unrun.
