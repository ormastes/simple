---
name: Deep Learning Reference
description: ML pipeline operators, dimension checking, ~> layer connect, training engine, LoRA, experiment tracking
type: reference
---

## Pipeline Operators
| Op | Name | Usage |
|----|------|-------|
| `\|>` | Pipe | `x \|> f` = `f(x)` |
| `>>` | Compose | `f >> g` = `λx. g(f(x))` |
| `<<` | Compose Back | `f << g` = `λx. f(g(x))` |
| `//` | Parallel | `f // g` runs both |
| `~>` | Layer Connect | NN pipeline with **compile-time dimension checking** |

## Layer Connect (`~>`)
```simple
val mlp = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)
# Type: Layer<[batch, 784], [batch, 10]>
```
Dimension mismatch → compile error E0502 with fix suggestion.

## Dimension Error Codes
E0501 Mismatch, E0502 LayerIncompat, E0503 RankMismatch, E0504 MatMulIncompat,
E0505 BroadcastIncompat, E0506 BatchMismatch, E0507 ChannelMismatch, E0508 SequenceMismatch

## Tensor Ops
- `@` matrix multiply (dim-checked), `.T` transpose
- `.+` `.−` `.*` `./` `.^` element-wise broadcasting

## Training Engine (`ml.engine`)
- `Engine(train_step)` — event-driven loop
- Events: `STARTED`, `EPOCH_STARTED/COMPLETED`, `ITERATION_STARTED/COMPLETED`, `COMPLETED`
- Periodic: `ITERATION_COMPLETED_EVERY(n)`, `EPOCH_COMPLETED_EVERY(n)`
- `engine.state.epoch/iteration/output/metrics`

## Experiment Tracking (`ml.tracking`)
- `Track.run(project, name, config, tags)` → `.log(metrics, step)` → `.finish()`
- Storage: `.simple/runs/{project}/{run_id}/`

## Progressive LoRA
- `add_lora(model, config)` — add trainable adapter
- `merge_lora(model, path)` — bake LoRA weights, freeze
- `progressive_lora_step(base, prev_loras, new_config)` — merge all + add new

## Key Locations
- Config: `src/lib/src/config/__init__.spl`
- Engine: `src/lib/src/ml/engine/__init__.spl`
- Tracking: `src/lib/src/ml/tracking/__init__.spl`
- Guide: `doc/07_guide/deep_learning/deep_learning.md`
