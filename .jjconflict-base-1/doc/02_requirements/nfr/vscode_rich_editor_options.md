<!-- codex-research -->
# VS Code Rich Editor NFR Options

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12

## NFR Option 1: MVP Throughput

**Targets**
- Extension activation under 200 ms warm
- First custom-editor paint under 250 ms for a typical demo file
- Edit echo under 120 ms for files under 500 lines

**Pros**
- Easy to hit with the current prototype
- Lowest implementation friction

**Cons**
- Too weak for large-file confidence
- Does not force correction of full-document edit churn

**Effort**
- `S`

## NFR Option 2: Production-Ready Rich Editor

**Targets**
- Extension activation under 150 ms warm
- First custom-editor paint under 200 ms for a representative `.spl` file
- Selection sync under 25 ms
- Block-local edit echo under 60 ms for typical math/image edits
- No duplicate-block rendering collisions
- No full-document rewrite for block-local edits in the steady state

**Pros**
- Strong fit for a real standalone extension
- Forces the key architecture hardening work
- Gives measurable performance and correctness gates

**Cons**
- Requires instrumentation and disciplined message/update flow

**Effort**
- `M`

## NFR Option 3: Large-Workspace Premium

**Targets**
- First paint under 150 ms warm
- Edit echo under 16 ms for common edits
- Smooth handling for files over 5k lines
- Multi-editor split support with deterministic sync
- Parser and rendering caches with explicit invalidation metrics

**Pros**
- Strongest long-term quality bar
- Appropriate if the rich editor becomes the default editing experience

**Cons**
- Overly ambitious for the current baseline
- Pulls performance engineering forward before core correctness is stable

**Effort**
- `L`

## Recommended NFR Target

Choose **Option 2: Production-Ready Rich Editor**.

It sets meaningful latency and correctness thresholds without forcing premature
optimization for huge files or split-editor workflows.
