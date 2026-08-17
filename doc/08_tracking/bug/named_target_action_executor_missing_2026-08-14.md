# Named target execution lacks dependency inputs and authoritative receipts

Status: ALREADY-FIXED (re-verified 2026-08-17: src/app/build/targets/target_executor.spl exists and src/app/build/targets/artifact_receipt.spl:27,147,163 implements DependencyArtifactInputV1 inputs plus canonical dependency-manifest digests/receipts)

The build CLI can parse, validate, deterministically resolve, and execute an
independent named target. The old CLI printed the plan and then fell through to
`cli_native_build`, which could perform a broad build unrelated to the declared
target while returning success.

The CLI now executes only a validated target-local action for dependency-free
targets and fails closed before side effects for dependency-bearing targets.
`simple build explain --target <name>` is read-only and explicitly reports that
digest evidence is unavailable and execution was not attempted.

Implemented containment:

- `target_executor.spl` translates each validated target into one scoped
  entry-closure native-build action, using a stable target-local output and
  cache namespace. Libraries emit archives; binary and test targets emit their
  declared executable artifact.
- Dependency-free selected actions execute without any broad native-build
  fallback or global cache clearing. A dependency-bearing closure is rejected
  before execution until dependency artifacts can be supplied soundly.
- Executor-level reuse is deliberately disabled because entry/tool/dependency
  artifact hashes do not cover private imported sources. Every action reports
  an Unknown closure digest and rebuilds; the compiler may still use its own
  authoritative internal incremental cache inside the target-local namespace.
- Each action writes a process-qualified candidate, verifies that a fresh,
  nonempty SHA-256-addressable artifact exists, and only then atomically
  publishes it. A stale declared output cannot satisfy the action.
- Execution reports selected, executed, rebuilt, and reused counts and fails
  closed on action or output-publication failure.
- Focused unit coverage proves action containment, stable paths, archive mode,
  Unknown/non-reuse behavior, and unsafe output rejection.

Remaining typed dependency-input blocker
----------------------------------------

Named targets with `depends` now fail closed with
`target-error: dependency-input-unsupported`. The pure-Simple native-build CLI
has no authoritative object/archive/manifest input option:

- `compile_targets.spl` recognizes `--source`, `--entry`, `--emit-object`, and
  `--emit-archive`, but no link/dependency input flag;
- both driver branches populate `CompileOptions.input_files` only from
  `_native_build_entry_closure(entry_point, source_dirs)` (or source dirs plus
  the entry when closure mode is off); and
- `cli_native_build_add_bootstrap_input` records those source paths, not
  already-produced artifacts.

An invented flag is unsafe because the decoder does not reject every unknown
option. The smallest sound extension is a required-value
`--input-manifest <path>` whose versioned records contain `producer_target`,
`artifact_path`, `artifact_kind` (`object`, `archive`, `smf`, or
`native-library`), `artifact_digest`, `link_export_digest`, and `abi_digest`.
The CLI must validate every record, bind it into `CompileOptions` as a distinct
typed artifact-input collection (not `input_files`), and make the linker consume
each declared artifact. Until then, dependency output consumption is Unknown
and cannot return success.

Publication collision audit
---------------------------

Execution compares every target's effective output path, including explicit
outputs and deterministic defaults, and rejects the first duplicate owner pair
before running an action. Canonical defaults use a SHA-256 label component;
legacy defaults retain their validated readable name.

Remaining blocker:

- Declared dependency targets currently impose dependency-first order, but
  their output artifacts are not passed as explicit inputs to the dependent
  `native-build` action. The compiler's entry closure remains the actual source
  dependency mechanism.
- The compiler does not yet return an authoritative imported-source closure,
  tool-behavior identity, or action receipt to this executor. Consequently the
  executor cannot prove compatible reuse and deliberately rebuilds every
  selected action with `closure-digest=unknown executor-reuse=disabled`.
- `targets.sdn` registers only the two independently buildable proof targets;
  it does not yet encode SCI projection, provider binding, compiler-provider,
  bootstrap, convergence, or DDC edges.

Unblock condition:

1. `native-build` accepts declared dependency artifacts (or a typed link/input
   manifest) and records their exact identities in the action.
2. The compiler emits a canonical imported-closure and tool-behavior receipt
   that the executor can verify before reuse.
3. The product graph declares the remaining configuration/provider/bootstrap
   targets with typed edges and focused mutation tests prove the expected
   rebuild closures.
