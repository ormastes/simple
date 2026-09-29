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

## Codex primary-source comparison addendum (2026-09-01)

<!-- codex-research -->

### ccache modes are three different evidence boundaries

The current [ccache 4.13.6 manual](https://ccache.dev/manual/4.13.6.html)
distinguishes:

- preprocessor mode, whose key includes preprocessor output, non-preprocessor
  options, and preprocessor diagnostics;
- direct mode, whose first lookup uses source/options and a manifest of headers
  observed on an earlier compile; and
- depend mode, which avoids preprocessing and learns inputs from `/showIncludes`
  or `-MD`/`-MMD` compiler output.

Those modes expose different failure closures. Direct mode cannot prove with
complete accuracy that a newly created higher-priority header would now win,
even though current ccache records include-directory existence to mitigate the
common case. Depend mode is only as complete as dependency output (`-MMD`
intentionally omits system headers). Preprocessor mode captures more effective
input state, but absolute paths, diagnostics, debug directories, and option
normalization affect relocation. Simple should therefore not offer a mode knob
that weakens evidence. Resolver-owned selected and negative candidates are the
minimum authoritative boundary.

The same manual also makes four traps explicit:

- compiler identity defaults to mtime+size, while content hashing is the safer
  bootstrap choice; plugins are inputs too;
- `__DATE__`, `__TIME__`, `__TIMESTAMP__`, and `__FILE__` couple results to
  ambient time or spelling, and sloppiness can knowingly permit stale results;
- inode/stat caches and newly modified inputs require race defenses because the
  compiler can read different bytes than the cache key observed; and
- `base_dir`, `hash_dir`, and debug-prefix mapping trade relocation hits against
  path-bearing output correctness.

Simple's snapshot/read-set design is stronger than these modes if it is wired:
same-handle frozen bytes, negative resolution witnesses, explicit compile clock,
and separate logical/presentation paths close the known holes. Unwired value
objects do not provide that strength to the current compiler.

### sccache makes daemon availability policy explicit

The official [sccache local-cache documentation](https://github.com/mozilla/sccache/blob/main/docs/Local.md)
states that multiple local servers racing on one store cause spurious build
failures. It also documents the same newly appearing header, time-macro, and
unknown-external-factor hazards for its preprocessor cache. The
[configuration documentation](https://github.com/mozilla/sccache/blob/main/docs/Configuration.md)
requires absolute base directories, exposes a maximum IPC frame length, notes
that some environment configuration requires server restart, supports
read-only tiers, and recommends a client-side mode where compilation remains in
the client and the daemon owns shared state. The
[README](https://github.com/mozilla/sccache/blob/main/README.md) makes local
compiler failover opt-in after server I/O failure.

The lesson for Simple is to make three policies non-ambient and independently
testable: who owns compilation, whether a cache write failure may fail a build,
and which daemon generation/configuration admitted the request. Simple's stated
fallback-to-compile policy is appropriate, but the native provider and process
tests must prove it; a pure state machine fed synthetic booleans is not daemon
evidence.

For distributed execution, sccache's
[quickstart](https://github.com/mozilla/sccache/blob/main/docs/DistributedQuickstart.md)
uses authenticated clients/servers and recommends TLS in front of the
scheduler. Authentication protects who may publish; it does not replace local
content and semantic verification.

### Bazel REAPI separates content integrity from action authority

The authoritative [Remote Execution API proto](https://github.com/bazelbuild/remote-apis/blob/main/build/bazel/remote/execution/v2/remote_execution.proto)
addresses CAS blobs by their own content, addresses action-cache results by the
digest of a serialized `Action`, requires `Command` and input-root digests, and
allows `do_not_cache` and a namespace salt to be part of action identity. It
also requires an action cache to keep referenced CAS blobs available for a
period after returning a result and advises clients to verify reassembled blob
digests.

Bazel's source-level [`remote_verify_downloads` option](https://github.com/bazelbuild/bazel/blob/master/src/main/java/com/google/devtools/build/lib/remote/options/RemoteOptions.java)
defaults to verifying hashes of remote downloads and discarding mismatches.
The [Remote Asset API](https://github.com/bazelbuild/remote-apis/blob/main/build/bazel/remote/asset/v1/remote_asset.proto)
says only trusted clients should be allowed to push URI-to-digest associations.
Together these are the relevant split: digest verification rejects corrupted
bytes; authenticated/authorized publication and complete action identity reject
validly hashed but malicious or semantically wrong mappings.

Simple currently recomputes artifact digests but not the remote result-manifest
digest and does not consume its promotion receipt. This is the classic gap
between CAS integrity and action-cache authority. Remote-main reads must remain
non-authoritative until canonical manifest bytes, complete semantic roots,
publisher trust, namespace, and receipt are verified locally before any
backfill or execution.
