<!-- codex-research -->

# Compiler semantic cache daemon and virtual summary: domain research

## Prior art and lessons

- [ccache 4.10 manual](https://ccache.dev/manual/4.10.html): direct mode hashes source plus previously discovered headers, but cannot detect a newly appearing higher-priority header. `base_dir` rewriting is brittle; timestamp/inode shortcuts and sloppiness trade correctness for hits. Simple must record selected and absent resolution candidates and expose no release-mode sloppiness.
- [sccache architecture](https://github.com/mozilla/sccache): a local client/server gateway amortizes startup and supports multiple storage tiers. Simple should copy the availability pattern, not move correctness authority into daemon memory.
- [Bazel Remote Execution API](https://github.com/bazelbuild/remote-apis/blob/main/build/bazel/remote/execution/v2/remote_execution.proto): separates immutable CAS blobs from action-cache mappings and commits canonical input-root, command and platform identities. Simple needs the same blob/action separation with language-specific semantic read sets.
- [Git loose-object format](https://git-scm.com/docs/gitformat-loose.html) and [repository layout](https://git-scm.com/docs/gitrepository-layout): immutable type/size/content objects can be shared independently of branches and worktrees, with reachability-based cleanup. Simple's hidden compile commit should follow this model without mutating Git refs.
- [rustc incremental dep graph](https://doc.rust-lang.org/stable/nightly-rustc/rustc_query_system/dep_graph/dep_node/) and [incremental persistence](https://doc.rust-lang.org/stable/nightly-rustc/rustc_incremental/): stable session-independent fingerprints and red/green dependencies enable reuse; failed sessions do not publish successful results. Simple should start with complete snapshot/read-set objects and leave a red-green query engine as an evolution path.
- [Clang modules](https://clang.llvm.org/docs/Modules.html) and [PCH internals](https://clang.llvm.org/docs/PCHInternals.html): serialized declarations/ASTs require option, header and dependent-module validation and multiple configuration variants. Simple AST decoding likewise needs bounded structural validation and frontend/schema identity.
- [Swift serialization](https://github.com/swiftlang/swift/blob/main/docs/Serialization.md): serialized modules/interfaces allow declaration loading without reparsing private bodies. Simple's `_tldr.spl` should be a deterministic inspection view over the same binary public-summary object.
- [Criterion statistics](https://bheisler.github.io/criterion.rs/book/analysis.html): performance gates need warmup, repeated samples, noise/outlier handling and confidence, rather than a single arithmetic mean.

## Holes Simple must close

1. Negative dependency discovery: record ordered resolution candidates and absence of higher-priority files/directories.
2. Snapshot consistency: hash and parse the same opened bytes; never mix pre-edit and post-edit sources.
3. Complete semantic identity: source, dependency interfaces, traits, AOP, macros/compile-time inputs, target/layout/features, compiler owners, provider bytes/configuration and runtime/link identities.
4. Transactionality: publish blob first, verify it, then atomically publish an action receipt. A failed compile cannot publish a success mapping.
5. Corruption and nondeterminism: quarantine corrupt objects and same-action/different-object results; never pick one nondeterministically.
6. Location independence: separate logical semantic paths from secure physical containment and presentation remapping.
7. Daemon equivalence: daemon restart/failure must yield identical artifacts and diagnostics through in-process fallback.
8. GC safety: active snapshots/builds hold leases; deletion uses tombstones/quarantine and at least two generations.

## ccache hole matrix and Simple mitigation

| ccache surface | Correctness/relocation hole | Required Simple mitigation and evidence |
|---|---|---|
| direct mode | keys previously used headers and can miss a newly appearing higher-priority include | snapshot the ordered resolver candidates, selected file and negative directory entries; mutation test creates the missing candidate |
| preprocessor mode | inherits preprocessor output/path/debug-prefix sensitivity and may obscure undeclared tool inputs | canonical semantic read set plus separate presentation paths; compare relocated-worktree outputs and diagnostics |
| depend mode | correctness depends on compiler dependency output completeness | Simple resolver produces its own complete read/negative-read witnesses; unknown reads make the action uncacheable |
| `base_dir` and debug paths | rewriting can be brittle and may make relative paths resolve differently | secure physical root authority plus logical repo-relative semantic paths and independent diagnostic remapping |
| compiler checks | mtime/content/path choices can miss wrapper, plugin or foreign-tool changes | hash admitted compiler owners, executable/tool bytes, provider/plugin content, ABI, capabilities and configuration |
| inode/stat shortcuts | same-size/same-mtime rewrites and inode reuse can create false hits | same-handle content hash is authoritative; stamps only avoid hashing after trust-domain and generation validation |
| time macros | `__DATE__`, `__TIME__` and similar ambient values are non-repeatable | declared deterministic compile clock or action is uncacheable/non-publishing |
| PCH/modules | validity depends on compiler options, dependent headers/modules and ordering | schema/compiler/config/read-set identities plus bounded AST/summary decoder and dependency manifest verification |
| response files/env | indirect flags and relevant environment may be omitted from a naïve key | expand and canonically hash response/config inputs; allowlisted env is declared and hashed, other ambient reads bypass cache |
| symlink/case/Unicode | aliases and normalization differ across filesystems/worktrees | anchored no-follow resolution, root containment, explicit filesystem case policy, NFC/collision rejection and relocation tests |
| hard links/cache mutation | mutable aliases can corrupt a shared cached result | immutable no-replace CAS publication, verified digest on read, quarantine on mismatch |
| remote storage | corrupt/untrusted remote values can be treated as hits | remote is an untrusted blob source; verify manifest, size, magic and digest locally before any action hit |

## Portable per-user cache locations

- Go centralizes this policy in [`os.UserCacheDir`](https://pkg.go.dev/os#UserCacheDir): Windows uses the local application-data directory, Darwin uses `~/Library/Caches`, and Unix uses `XDG_CACHE_HOME` or `~/.cache`. Simple's existing `std.env.platform.get_cache_dir` already follows the same useful shape; cache consumers should call a common application accessor instead of reproducing OS branches.
- Python's [`platform` standard-library module](https://docs.python.org/3/library/platform.html) exposes host identity but no equivalent application-cache-directory API. That omission is a warning against making every Simple application invent its own `HOME`/`APPDATA` convention.
- Windows exposes `FOLDERID_LocalAppData` as a per-user local application-data known folder in the [Known Folder ID reference](https://learn.microsoft.com/en-us/windows/win32/shell/knownfolderid). `%LOCALAPPDATA%` is a compatibility input, while a native host implementation should ultimately resolve the known folder and then enforce containment by opened handles.
- The [XDG Base Directory Specification](https://specifications.freedesktop.org/basedir-spec/latest/) requires `XDG_CACHE_HOME` to be absolute and defaults it below `$HOME/.cache`. Simple should likewise accept `SIMPLE_CACHE` only as an absolute physical root; a relative override is ambiguous across daemon/client working directories and must fail closed.

Selected common API consequence: the pure selectors `user_local_location_v1` and `cache_location_v1` keep platform policy testable, while the public environment facade exposes `get_user_local_dir()` and `get_cache_location(app)`. Only the latter reads the single `SIMPLE_CACHE` override. None performs security admission. `HostPathAuthorityV1` separately converts the selected physical root into an anchored capability, so convenient platform selection cannot be confused with symlink/junction safety.

## Performance methodology

Measure cold, unchanged warm, private-body edit, public-signature edit, AOP/trait edit and link lanes separately. Use one warmup and at least seven alternating baseline/candidate pairs on a quiet runner. Compute both the median and 20%-trimmed mean over per-pair candidate/baseline ratios. With coefficient of variation at most 5%, fail when both exceed 1.10 and pass when both are at most 1.10. Report `INCONCLUSIVE` when they disagree across 1.10, variance exceeds the bound, or admitted-runner/evidence requirements are incomplete; permit one bounded quiet-runner retry and block release if it remains inconclusive. Pin source/compiler/provider/cache/baseline digests and record wall, CPU, RSS, hit/miss/reparse counts and output identity.
