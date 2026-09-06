# Feature: standalone-target-build-no-bootstrap

## Raw Request

Do not start compiler bootstrap from Phase 1 for standalone tools. Start from
the last existing phase such as Phase 3; separate target products such as Office
from rebuilding Simple; update docs, guide, SPipe skill, LLM wiki, process, and
the relevant script/code.

## Task Type

code-quality

## Refined Goal

Make standalone target-product builds reuse only an admitted existing Phase 3
compiler and fail closed without initiating compiler bootstrap.

## Acceptance Criteria

- AC-1: A canonical resolver accepts only a provenance-admitted Phase 3 compiler
  and never invokes bootstrap stages.
- AC-2: The Office target wrapper uses that resolver with strict no-stub guards
  and cache/output paths outside `build/bootstrap`.
- AC-3: A focused contract check proves the wrapper's target-only policy.
- AC-4: Build guide, SPipe procedure, LLM process wiki, Gemini command, and
  generated operator manual describe the same boundary.

## Scope Exclusions

- Producing a new compiler, deploying Stage 4, or proving ARM64 QEMU evidence.

## Cooperative Review

N/A — bounded process/script change; no independent code surface needs a sidecar.

## Phase

dev-done

## Log

- dev: Created target-only build workflow state.
