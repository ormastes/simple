# Seed `run` mode: public summary projector refuses a single fact ("cannot be ordered")

Status: open; verify on the self-hosted binary once Stage 3 exists.
Found 2026-10-24 (PR #4362).

## Symptom
`project_public_summary_v1` (src/compiler/10.frontend/cache_artifact/public_summary_projector.spl)
returns `Err("public summary dependency graph cannot be ordered")` for ANY
input under the seed's `run` command -- even one Forward + Declaration pair
with no dependencies. The identical call succeeds under the seed's `test`
command (module_public_summary_facts_v1_spec 3/3). Consequence: `simple tldr`
run through the seed writes companions with no `summary` section.

## Repro (seed `run`)
```
use std.common.crypto.sha256.{sha256_text}
use compiler.frontend.cache_artifact.public_summary_projector.{FrontendPublicFactKindV1,
    FrozenPublicFactV1, PublicSummaryProjectionInputV1, project_public_summary_v1}
use compiler.common.cache_contract.snapshot_contract_v1.{LogicalSourcePathV1, PathSemanticsV1}
fn main() -> i64:
    val b = "pub extern fn f0() -> i64"
    val facts = [
        FrozenPublicFactV1(fact_kind: FrontendPublicFactKindV1.ForwardDeclaration, stable_symbol_id: "sym:f0",
            canonical_bytes: b, is_public: true, contains_executable_body: false,
            contains_private_source: false, dependency_symbol_ids: []),
        FrozenPublicFactV1(fact_kind: FrontendPublicFactKindV1.Declaration, stable_symbol_id: "sym:f0",
            canonical_bytes: b, is_public: true, contains_executable_body: false,
            contains_private_source: false, dependency_symbol_ids: [])]
    match project_public_summary_v1(PublicSummaryProjectionInputV1(snapshot_id: sha256_text("s"),
            logical_path: LogicalSourcePathV1(repository_namespace_digest: sha256_text("r"),
                module_relative_utf8: "m.spl", path_semantics: PathSemanticsV1.CaseSensitiveNfc),
            source_blob_digest: sha256_text("x"), compiler_owner_digest: sha256_text("c"),
            grammar_digest: sha256_text("g"), facts: facts)):
        case Ok(_): print "ok"
        case Err(e): print e
    0
```
Seed `run` prints `public summary dependency graph cannot be ordered` for
N = 1, 2, 3, 5, 8, 12, 20 facts.

## Analysis
With no dependency edges every fact is its own group, so
`_forward_graph_order_v1` must always find a ready group; reaching the
"cannot be ordered" branch means the loop state (`group_for` / `emitted`
comprehensions, or `break` inside `for` inside `while`) is mis-evaluated by
the seed `run` lane. Lane-specific, not data-specific.

## Next
Re-run the repro on the self-hosted Stage 3 binary. If it passes there, this
is seed-only; if not, minimise `_forward_graph_order_v1`.
