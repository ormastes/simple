# Minimal-Bootstrap Feature Development

This is the authoritative policy for choosing the build closure during normal
feature development. Bootstrap stage mechanics remain in [build.md](build.md);
provider and composition architecture belongs in this guide.

## Default architecture

Simple converges on three independently replaceable layers:

1. `simple-core`, the stable configuration reader, provider loader/query host,
   capability enforcer, diagnostics surface, and recovery entrypoint.
2. `SimpleCompositionImageV1` (`.sci`), immutable validated data containing
   provider bindings, commands, applications, associations, policies, targets,
   and exact artifact identities.
3. Provider artifacts (`.smf`, `.so`, `.dylib`, or `.dll`) implementing
   versioned interface groups through `SimpleProviderQueryV1`.

Configuration is inert data. Runtime startup must not scan configuration
directories, merge text overlays, construct shell commands, or compile a
missing provider. Text configuration is resolved before startup and projected
into one SCI; it must not create a second application or launch manifest.

The first stable leaf contracts are `SimpleCliCommandV1` and
`SimpleAppLaunchV1`. Language-internal `any`, AST, HIR, MIR, allocator-owned
collections, exceptions, and implicit object layouts must not cross a stable
provider ABI. Start compiler decomposition with one coarse opaque driver
provider; do not dynamically split lexer, parser, HIR, or MIR merely to reduce
the core closure.

The first coarse compiler boundary is implemented by
`compiler.driver.driver_provider_contract_v1` and the in-process
`CompilerDriverProviderInProcessV1` adapter. Sessions, requests, and results
cross that contract only as monotonic numeric handles; compiler options,
diagnostics, and internal IR remain provider-owned. The in-process adapter is a
contract/proof slice, not dynamic-loader evidence: its query reports no locked
implementation digest. Dynamic or SMF dispatch must fail closed until an
admitted artifact supplies a process-callable query entry. Consequently the
concrete bootstrap driver import remains in place; its exact unblock evidence
is tracked in
`doc/08_tracking/bug/compiler_driver_v1_bootstrap_activation_blocked_on_callable_loader_2026-08-14.md`.

## Development build selection

Command/product classifier:

- CLI-0 is static `simple-core`: `--help`, `--version`, `config verify`,
  `provider inspect`, and `doctor`.
- CLI-1 is the essential provider: `run`, `compile`, `native-build`, `build`,
  `check`, `test`, `config`, and `query`.
- CLI-2 is extended providers: lint/fmt/fix/duplicate/spec, MCP/LSP, stats,
  SBOM, docs, IDE, Office, UI, browser, and other optional tools.

B1/B2/B3 mean Rust seed, pure-Simple bootstrap compiler, and admitted self-host
compiler. P0/P1/P2/R0 mean simple-core, essential CLI, optional providers, and
release bundle. B1 is bootstrap-only; B2/B3 use explicit admission. These names
do not relax the stage-scoped evidence rules below.

Start with the smallest named computation that can decide the change:

1. Run the focused unit, integration, or system scenario once.
2. Build the named target containing the changed code.
3. Rebuild only the changed provider artifact.
4. Recompile only the affected SCI projection when its locked identity or
   configuration changes.
5. Rebuild a compiler stage only when compatibility evidence proves that the
   admitted producer cannot satisfy the required contract.
6. Invoke a full bootstrap only for a typed bootstrap incompatibility or an
   explicit release/trust target.

A path under `src/compiler/**` is not itself a bootstrap reason. A private
compiler-provider body change rebuilds that provider and outputs whose declared
tool-behavior dependency changed. An interface change rebuilds consumers of
that interface group. Unknown compatibility never authorizes reuse; it causes
the smallest conservative producer or consumer rebuild that can establish
evidence.

The current T0/T1/T2 terminology may describe the cost of an existing build,
but it must not override the compatibility decision above. Do not clear global
caches, silently execute the Rust seed, use `one-binary` as the normal
development product, or turn a cold worktree into an implicit bootstrap.

### Admitted Stage 2 and Stage 3 tools

Focused pure-Simple compiler, interpreter, or loader development may use an
explicitly admitted Stage 2 or Stage 3 Simple binary when the requested command
is supported by that stage. Before execution, record the exact absolute binary
path, content hash, stage, producer/provenance receipt, and supported-command
set. Put target output and cache in a lane-specific isolated directory; do not
write through deployment or shared bootstrap outputs.

Admission is fail-closed. A missing/stale receipt, hash mismatch, unknown stage,
or unsupported requested command stops the lane. It must not silently select a
different binary, start another bootstrap stage, or fall back to the Rust seed.

Evidence is labeled with its stage and may satisfy acceptance criteria that
explicitly concern that Stage 2 or Stage 3 compiler/interpreter/loader behavior.
It does not establish a deployed Stage 4 CLI, general SPipe/docgen/test-runner
operation, release readiness, self-host convergence, DDC, or another host's
behavior. Those claims require their own admitted binary and evidence.

## Required build receipt

Initial acceptance is structural: report modules parsed, typed, and lowered;
objects generated; providers packaged; links performed; SCI sections
regenerated; and cache hits/misses. Configuration-only changes have zero code
work. Timing and RSS may be recorded with host and producer labels but are not
initial pass/fail thresholds. No bootstrap process may start before the planner
emits and validates its typed reason.

Current CLI boundary: `simple build explain --target <name>` validates the
declared target graph and prints its deterministic dependency plan. It reports
`digest-evidence=unavailable` and `execution=not-attempted`; this is planning
evidence, not a rebuild receipt. `simple build --target <name>` now executes
only the deterministic resolved closure through target-local output/cache
paths. Each action publishes through a fresh process-qualified candidate;
executor-level reuse remains disabled and reports `closure-digest=unknown`
until the compiler supplies an authoritative imported-closure receipt. Declared
dependency outputs are not yet explicit native-build inputs. These remaining
executor gaps are tracked in
`doc/08_tracking/bug/named_target_action_executor_missing_2026-08-14.md`.

`build-explain` evidence for a changed compiled component records:

- requested target and changed files;
- changed interface groups;
- implementation, compile-interface, ABI, compile-semantic, and tool-behavior
  digest deltas;
- selected rebuild closure;
- cache reused and rebuilt counts;
- `bootstrap_required`; and
- a non-empty typed `bootstrap_reason` whenever bootstrap is required.

Compatibility is `Exact`, `Compatible`, `Unknown`, or `Incompatible`.
`Exact` and proven `Compatible` permit reuse. `Unknown` rebuilds conservatively.
`Incompatible` escalates only to the smallest stage capable of satisfying the
contract.

Allowed bootstrap reasons are explicit compatibility, availability, or trust
events such as a missing/corrupt/unsupported seed, an admitted compiler unable
to parse or lower a required bootstrap feature, a bootstrap runtime or artifact
format major change, a bootstrap-core interface major change, self-host
convergence, release trust verification, or diverse double compilation. App
metadata, command registration, provider-private code, documentation, cache
absence, or merely living under `src/compiler/**` are not reasons.

The executable gate is two-step and fail-closed. `simple build bootstrap` is a
receipt-only planner; it never starts a stage:

```text
simple build bootstrap --bootstrap-reason=self-host-convergence-check \
  --bootstrap-receipt=build/bootstrap/reason.receipt
scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=build/bootstrap/reason.receipt
```

The staged driver rejects a missing, malformed, unknown, or `None` receipt
before Stage 1. Ordinary `simple build`, configuration targets, and provider
targets never manufacture this receipt or select Stage 4. Direct/ad-hoc callers
must use the same planner or receive `bootstrap-policy-error:
reason-receipt-required`. Windows forwarding and admitted Stage 3 resume enter
the same guarded driver. The v1 receipt is a canonical provenance marker, not a
cryptographic authorization token; host users able to modify arbitrary files
can forge it. Cryptographic or OS-mediated authorization remains out of scope
until bootstrap execution has a dedicated privilege boundary.
Stage-limited workflows bind the receipt to their exact target: use
`--bootstrap-target=//bootstrap:stage3` with
`--resume-stage3-from-admitted`. The default planner target is
`//bootstrap:stage4`. `--validate-bootstrap-receipt` validates the binding and
exits with `execution=not-attempted`.

## Expected containment

| Mutation | Rebuild |
|---|---|
| App name, shortcut, or association | SCI projection only |
| CLI alias | SCI projection only |
| Provider-private implementation | Provider; SCI only if its locked digest changes |
| Optional interface extension | Provider and consumers that opt in |
| ABI major break | Provider and consumers selected for that major |
| Backend optimization | Backend provider and affected produced artifacts |
| Compiler public interface | Direct interface consumers |
| Bootstrap runtime/artifact-format major | Relevant bootstrap stage/readers |
| Documentation | No compiled artifact |

Every containment claim needs a receipt or executable scenario showing the
selected closure and proving the unchanged core/compiler identities. A missing
receipt is missing evidence, not permission to broaden the build.

## SPipe and release boundary

Normative implementation order is P0 cheap decisions, P1 core extraction, P2
CLI configuration, P3 essential provider, P4 leaf providers, P5 per-module
cache, P6 compiler engine provider, P7 full product composition, and P8 release
bootstrap. Later work may prepare interfaces but cannot bypass earlier receipts.

SPipe plans declare the target, owned/forbidden paths, changed interface groups,
expected rebuild closure, and bootstrap reason before parallel work begins.
Executable scenarios use stable flow names such as `compile_composition`,
`load_unchanged_core`, `dispatch_provider`, and `explain_rebuild`; unfinished
scaffolds fail explicitly.

Self-host convergence and DDC remain explicit release/trust targets. Normal
feature verification must not invoke them as a generic final confidence check.
Release consumes verified SPipe evidence and must not repair missing
composition, containment, or documentation evidence.
