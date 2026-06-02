# SPipe LLM Fine-Tune Process Architecture

## Pattern

Use SPipe as the reusable process module and keep host-specific attempts in the
host repository. Shared process docs, templates, domain experts, and tool
experts live in the SPipe project. Host docs link to those shared roots and keep
project-specific feature/layer experts locally.

## Layers

Layer 1: Record contracts.
Defines attempt, model, data source, training script, eval result, and retry
decision records.

Layer 2: Process orchestration.
Runs research, data download, base model selection, tuning method selection,
training, eval, and retry routing.

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
