# Scoped typecheck consumer escape audit and native authority gate

Status: focused static audit of commit 127a54bb and its actual consumer
dependencies. No native jobs were run and no frozen campaign source was edited.
Native 31-check acceptance remains pending the campaign owner's serialized slot.

## Actual collector allocation owners

The collector creates a fresh `HmInferContext.with_builtins()` for each module.
`30.types/type_infer/context.spl:new` owns its environment, substitution,
errors, dimension solver/check generator, trait solver, function bounds,
narrowing state, mutability indexes, effects and symbol indexes. `with_builtins`
calls `new` and registers identity/print/len only into that new context. It does
not initialize a singleton builtins map. Fresh inference variables and schemes
stay in that same context. `DimSolver.new`, `DimCheckGenerator.new`,
`TraitSolver.create`, `AssocTypeResolver.create` and `NarrowingContext.new`
likewise construct fresh owner fields rather than retaining a global cache.

The HM implementation and dimensional/narrowing owners have no mutable Simple
module globals. The inference entrypoint's module/function symbol lookup reads
the decoded module's own symbol table, and registrations/substitutions/errors
write `self` fields on the freshly created HM context. Formatting is the
extracted original error formatter; related spans/types become text before
they enter the retained receipt. No type/error object is retained by the API.

`frontend_diag_enabled` directly reads `SIMPLE_FRONTEND_DIAG` through
`rt_env_get`. In `runtime_native.c`, that function copies the environment value
into a new managed string and frees its C key buffer; it does not install an
environment memo. That temporary string belongs to scratch. The enabled walk
creates `HirFrontendWalker` per call, with local variant/pending/suggestion
dictionaries and findings; the default consumer keeps optional Any tracking
off as before. Its imported `_mexh_is_suspect_case_name` is a stateless text
classification helper. Sorting returns a local finding list. Only rendered
finding strings enter the receipt. No walker, findings object, enum/symbol
index, or imported provider table escapes.

`check_module_visibility` creates a local `VisibilityChecker`, walks the real
function bodies and reads their symbol tables. Warning records and boundary
path strings belong to that local checker. Its directory checks call
`file_exists`; the native implementation uses temporary C path storage and
does not retain a managed path memo. `DirManifest.new` and friend checks use
local fields. There is no Simple module-level visibility/friend manifest cache
in the consulted owners.

## Conditional trait publication is not a lazy memo

The trait facade is not globally pure: `25.traits/trait_solver.spl:add_impl`
and `add_obligation` can publish trait reverse-reference facts into
`00.common/cache/reverse_reference_facts.spl`. Those globals are not covered
by the HirLowering 49-root phase memo carrier. It would be incorrect to include
every imported trait API in the text-only escape claim.

The actual collector's fresh solver starts with empty traits, impls,
trait-method indexes, obligations and function-bounds map. `infer_module`
registers symbol mutability, declares function signatures, infers bodies and
solves dimensional constraints; it does **not** call
`collect_traits_from_module`, `collect_impls_from_module` or
`collect_function_bounds_from_module`. Those are the registration owners that
could populate the prerequisite maps. `with_builtins` does not populate them
either. Therefore, a call body's
`generate_obligations_for_function_call` exits on missing function bounds;
`generate_obligation_for_method_call` cannot find a declaring trait in the empty
trait-method index, and its documented fallback does not publish an obligation.
`TraitSolver.create` itself only constructs local empty fields. No current
collector path reaches `add_impl` or `add_obligation` publication.

This is a source reachability proof about this exact fresh-context consumer,
not evidence that trait registration/validation is enabled here or permission
to disable another validator. If future consumer work enables those collection
calls, its lease must adopt the existing reverse-reference module
begin/seal/publish/abort transaction. Begin redirects new facts to the scoped
module batch; paused seal promotes only that batch/Option carrier and removes
lookup scratch; publication follows scope end. Promoting the whole phase
registry or silently disabling facts would break ownership or completeness.

No reachable lazy persistent Simple memo initialization was found in the
current HM/frontend/visibility consumer. No extra promotion owner or source
fix is justified by the audited call paths. The adapter already initializes
the actual persistent frontend cache identity before scratch, clears the
cache warning alias while paused, and promotes the cache's dynamic I/O reason
alongside its enumerated diagnostic escapes. Runtime allocator bookkeeping
is managed by the existing scope mechanism and is still subject to native
lifetime acceptance, rather than inferred from this static audit.

## Enforced canonical launcher prerequisites

`scripts/bootstrap/tests/hir-body-typecheck-lease-native.shs` accepts
`--preflight` or `--run` followed by canonical producer source root, frozen
fixture source root, exact owned Stage3 lane, and a fresh external evidence
directory. Preflight starts no Simple compiler/fixture; optional materialized
owner validation uses the existing PowerShell/native interop owner. It derives the admitted
candidate, admission receipt, source/runtime/tool snapshots, sanity/receiver
receipts/log and runtime authority from that lane and invokes the existing
full 21-argument Stage2 admission verifier. Status/SHA-shaped environment values
are never used as authority.

It then requires the existing adjacent `runtime-capsule.env` binding and calls
`phase2-runtime-binding.shs resolve`. That owner verifies the selected capsule
against the exact admission, runtime leaves and canonical current source
snapshot. The launcher does not publish a binding or mutate frozen producer
files. Missing/stale bindings fail preflight; they do not fall back to a label,
arbitrary runtime path or mutable target directory. The selected sealed capsule
is reverified by the canonical capsule verifier and its producer/layout must
match the exact admitted Windows MSVC compiler.

The fixture tree defaults to Git-clean. An explicit
`SIMPLE_HIR_LEASE_FIXTURE_LINKS_RECEIPT` enables the canonical materialized owner
mode: staged changes are refused, every changed tracked path must be an exact
HEAD mode-120000 alias, and every untracked path must lie under such an alias.
The existing native `bootstrap_stage3_materialized_git_state` then validates
the exact fixture root and supplied receipt. The Git gate alone cannot prove
alias targets; a plain directory or copy that passes that delta gate still
requires canonical filesystem/receipt authority. General dirty fingerprints
from the native owner are insufficient without the additional alias-only gate.
Before/after HEAD, Git deltas, receipt bytes and native owner snapshots must
match. This permits receipted canonical materialization without accepting
source edits, and never materializes or mutates a live frozen fixture tree.

The current revision has three source aliases, all under `src/app` for Trace32
tools, and none are imported by the lease fixture or compiler/lib sources.
Compiler/std imports use numbered-directory resolution, not these Git aliases.
A separate clean fixture owner with whole `src`, `config`, required scripts and
the three committed fixture files is therefore a valid default candidate;
actual native dependency closure still must pass. A sparse tree missing
`config/var.sdn` is not ready. This harness hashes that actual committed selected
configuration alongside the fixture files and refuses its absence.

The fixture's canonical owned-source snapshot and
the actual main/provider/mismatch fixture files produce the closure digest;
the digest is not a hash of a label or only a Git revision. Canonical snapshots
exclude vendor/target caches. Evidence retains these bytes plus the actual
admission, binding and capsule receipt. `--run` compiles the fixture through
that exact producer using positional `native-build`, the selected capsule,
private cache/storage directories and the unchanged enforced 5859375 KiB cap
and 600-second compiler timeout. Compiler/source/capsule identities are checked
again before execution. The executing fixture has its own SHA-bound frontend
scope; the two new runtime receipt environment values and the closure digest
are assigned from admitted/read-and-hashed bytes by the launcher, overriding
arbitrary inherited values. It requires exit 0 and the positive 31-check output.

The launcher passed Bash syntax validation. A preflight-only negative control
supplied SHA-shaped runtime/closure environment values and an unproved
admission packet; the actual admission replay refused it with exit 96 before
any compiler or program started. Evidence is retained under
`C:/dev/simple-phase3-hir-memory-evidence/body-typecheck-lease/authority-gate-negative/`.

The actual shared Git gate passed eight controls: clean owner, non-alias source
edit refusal, arbitrary new source refusal, admitted alias-only Git delta,
alias delta refusal in default clean mode, staged alias refusal, descendant
delta under a HEAD alias, and refusal of unrelated source alongside that
descendant. Those PASS controls qualify the Git filter only; they never call or
substitute the materialized owner validator. Evidence is retained under
`C:/dev/simple-phase3-hir-memory-evidence/body-typecheck-lease/fixture-git-gate-regression/`.
Positive canonical materialized receipt acceptance remains pending.

No preflight or native PASS for a real new producer is claimed here. A missing
canonical binding is a concrete prerequisite for the campaign owner to resolve
through its existing publication workflow; this harness never creates it in a
live frozen tree.
