# Dependency resolver imports an unresolved directory-probe facade

Canonical ID: `dependency_resolution_dir_exists_facade_missing_2026_11_06`.
Severity: P1. Status: source repair implemented; executable verification pending.

Linux Phase Ladder run42208359530, job127860566362 failed the Phase2 HIR
boundary at source pin `bbfe33dd9f1d1c0007f79788b5f8ff67b2fddbd0`:

    unresolved name: dir_exists
    src/compiler/00.common/dependency/resolution.spl:117:31

The closure contained1593 modules. This is a real failed compiler boundary,
not a successful Phase2 receipt. Exact producer/build authority is being
recovered from the CI artifacts; this report does not infer qualification from
a filename, stage label or linked binary.

The defect remains in release source
`587116dc5d1fb9a3f53270d6b10de2fc56db423a`.
`resolve_segment_with_numbering` imports `file_exists` and `dir_exists` from
`std.io`. The actual diagnostic identifies the selected facade as
`lib.nogc_async_mut.io`: it exports the directory-probe name but has no
declaration or resolvable explicit forwarding route for it. Its self-alias
`use std.io.*` imports do not establish that missing provider.

The resolver now imports both operations through the existing
`std.io_runtime` facade. That facade explicitly forwards them to the standard
runtime owner and is already used for the same checks by compiler source-root
handoff and cache modules. This is an importer correction, not a global
variant-selection pin or an expansion of the broken I/O facade. Resolver
compatibility-helper control flow and its unimplemented numbered-directory
fallback remain unchanged. The model-path repair below addresses a separately
observed blocker in the same owner.

The regression fixture is
`test/fixtures/compiler/dependency_resolution_filesystem_probe/main.spl`.
It imports and calls the actual resolver owner, requires real directory/file
probes to distinguish the fixture directory, its source file and an absent
path, then checks existing directory/file/missing compatibility results. Run
from the repository root. Required native stdout is exactly:

    dependency resolution filesystem probes OK

Its central regression is successful self-hosted name binding and native
compilation of the actual owner; a seed's flat-name behavior is not a valid
substitute. At the original importer-only checkpoint, native compile/run was
UNRUN; the failed qualification attempts below supersede that observation.
The original1593-module HIR build and required core/MCP gates remain UNRUN.
No bootstrap restart or broader Phase2/Stage3 completion is claimed.


## Native qualification and model-path repair — 2026-11-06

The actual pure-Simple P1 producer is SHA-256
`e05b9162248105144b99ae85b1a88431e0983bcf0ac0e9a63ebc1307efe0d6bb`.
Its fresh compiled-Hello PASS is retained independently; it has no qualified
`test`/`check` runner. The following attempts used exact source
`1f953da5502dc9dc7a6c22c4ab33728d3cba1801`, LLVM23.1.1 and a unique supported
`SIMPLE_CACHE` in an isolated Linux volume. Receipt-bound checked-out source
trees are runtime `0f712ab9be85f31e65464e76345b76b09d91bed2` and library
`6b4d7001e3c5039a7c039b4dca0cad091247b3e7`. These are source inputs, not proof
of target-runtime linkage. The prior Hello used B60 runtime-source tree
`e636c526ce00f266b4221c0082d701b5fc2a8b39`. Native codegen/linking was never
reached in cycles3–5, so the selected target link-runtime is UNKNOWN and no
qualification of the current target runtime is claimed.

- Shared cycle3 stopped before compilation: first-checkout compile-event
  journal missing. The producer explicitly requested supported cold inventory
  initialization.
- Cycle4 enabled that initialization but source admission refused the directory
  alias inventory. Cold initialization inventories all of `src`, `test`, and
  `examples/10_tooling`; the narrower checkout omitted the targets of three
  real `src/app` directory aliases. This was an input-materialization defect,
  not proof of a compiler or filesystem-provider defect.
- Before cycle5, all canonical cold roots were materialized at the same source
  revision. All11 tracked aliases resolved inside the checkout, with no nested
  target aliases or tracked source changes. Cycle5 passed admission, completed
  HIR/monomorphization for52 modules, then failed MIR:51 succeeded,1 failed.
  The exact failure was unresolved method `name` at
  `src/compiler/00.common/dependency/resolution.spl:106:23`. Native codegen,
  linking and fixture execution were not reached. Exit1, no OOM; peak cgroup
  memory4937678848 bytes under an8GiB/2CPU limit.

This newly reached MIR failure is a genuine source defect. `Segment` declares
`name: text`; the direct owner imports only the filesystem operations and has
no `Segment.name()` method or imported extension. The same invalid method call
already exists in the producer's source revision, so historical source alone
cannot establish working support.

The repair reads `segs[i].name` as the declared field. It also corrects a
misplaced trailing initializer expression: the shared path builder previously
ended with both `path` and `path + "/__init__.spl"`, so its last expression
polluted the file form with `/__init__.spl.spl`. The builder now returns the
bare path, and only `to_dir_path` appends `/__init__.spl`.

The authority is `src/verification/module_resolution/src/ModuleResolution.lean`
definitions `toFilePath` and `toDirPath`: file form is `root/a/b.spl`, directory form is
`root/a/b/__init__.spl`. The existing commented migration catalog agrees but
is not executable evidence.

The native fixture retains filesystem guards11–17 and adds exact two-segment
file/directory paths plus all four real in-memory resolution outcomes:
Unique File, Unique Directory, Ambiguous with both payload paths, and NotFound.
Every mismatch exits nonzero; the existing success marker is emitted only by
the final expected NotFound branch. The focused SSpec now has real assertions
instead of the prior `pending_reason` length checks. Its manual is an authored,
unrun projection; neither SSpec execution nor docgen is claimed.

Shared cycle6 remains NOT STARTED pending immutable-source review and explicit
resource coordination. The cause ceiling is6, including all prior attempts;
changing source revisions or worktrees does not reset it. Full original HIR,
core/MCP, SPipe execution and broader compiler qualification remain pending.
