# SPipe LLM Fine-Tune Process Architecture

## Pattern

Use SPipe as the reusable process module and keep host-specific attempts in the
host repository. Shared process docs, templates, domain experts, and tool
experts live in the SPipe project. Host docs link to those shared roots and keep
project-specific feature/layer experts locally.

## Layers

Layer 1: Record contracts.
Defines attempt, model, data source, training script, eval result, and retry
decision records. Contracts are reusable SPipe knowledge; concrete records stay
in the host `.spipe/llm-finetune-process/` directory.

Layer 2: Process orchestration.
Runs research, data download, base model selection, tuning method selection,
training, eval, and retry routing. Orchestration is exposed through the SPipe
CLI and MCP surface so different hosts can use the same process.

Layer 3: App/server development integration.
Links each generated or retuned LLM-backed app/server implementation to the
attempt record that supplied the model or implementation assistant.

Layer 4: Verification.
Checks records for real scripts, model references, eval results, and retry
decisions before release.

## Retry Flow

Verification classifies failures as app implementation, prompt/retrieval,
training data, base model, tuning method, or environment. SPipe then retries the
appropriate phase: implementation, data research, model selection, tuning, or a
different non-training approach.

## Mount Model

The separated SPipe project has two host-visible mounts:

- `.spipe/spipe`: compatibility submodule for reusable SPipe assets.
- `examples/spipe`: standalone SPipe example tree tracked by the parent repo.

Host links:

- `.spipe/spipe_project` points to `examples/spipe`.
- `.spipe/doc` points to the host process doc root from `.spipe/config.sdn`.
- `.spipe/domain_expert`, `.spipe/template`, `.spipe/spipe_docs`,
  `.spipe/project_expert/spipe`, and `.spipe/tool_expert/spipe_submodule`
  point to common roots inside the SPipe project.

The default process doc root is `doc/llm_process`; Simple overrides it with
`doc/00_llm_process`.

## Index Invariant

The parent repo must track `.spipe/spipe` as a gitlink. In this checkout,
`examples/spipe` is intentionally tracked as normal parent-repo files so local
examples remain visible without requiring a second SPipe gitlink. The
`scripts/check-spipe-submodule-gitlinks.shs` checker and the matching
PowerShell script verify this mixed invariant and repair only `.spipe/spipe`.

## Hot Path / Performance

The process does not add hot request handlers to Simple runtime, MCP, or LSP
services. SPipe CLI commands operate on small `.sdn` registries and explicit
docs. Repeated full-tree scans are limited to verification/build guards, not
runtime app/server request paths.
