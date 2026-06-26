# Experiment Tracking Library Research

**Date:** 2026-02-01
**Purpose:** Survey existing ML experiment tracking tools and design a Simple-native library

---

## What exists today (grouped)

### 1) Experiment tracking (metrics, params, runs UI)

| Tool | Typical usage | Notable features | License | Stars |
|------|--------------|------------------|---------|-------|
| Weights & Biases (wandb) | cloud-first tracking for teams | rich UI, reports, sweeps; self-host options | MIT (SDK repo) | ~10.8k |
| MLflow | self-host tracking + model registry | tracking server, artifacts, registry; strong "platform" shape | Apache-2.0 | ~23.9k |
| AimStack (Aim) | self-host UI for many runs | fast local UI; good comparison workflows | Apache-2.0 | ~6k |
| ClearML | tracking + orchestration + serving | "suite": tracking + pipelines + data mgmt + more | Apache-2.0 | ~6.5k |
| Neptune AI | tracking client (cloud product) | client lib + platform integrations | Apache-2.0 | ~622 |

**Minimal training-loop example (common pattern):**
```
run = tracker.init(project="proj", config={"lr": 1e-3, "bs": 64})
for step, loss in enumerate(train()):
    run.log({"loss": loss}, step=step)
run.finish()
```

### 2) Config management (reproducibility, overrides, composition)

| Tool | Typical usage | Notable features | License | Stars |
|------|--------------|------------------|---------|-------|
| Meta Hydra | launching + composing configs | config groups, multirun, CLI overrides | MIT | ~10.2k |
| OmegaConf | underlying config object model | hierarchical merge, structured configs | BSD-3-Clause | ~2.3k |

**Minimal Hydra-ish override example:**
```
python train.py model=resnet data=cifar lr=0.001 trainer.max_epochs=50
```

### 3) Data / artifact versioning

| Tool | Typical usage | Notable features | License | Stars |
|------|--------------|------------------|---------|-------|
| Treeverse DVC | Git-like versioning for data/models | local experiment tracking, pipelines, remotes | Apache-2.0 | ~15.3k |

### 4) Sweeps / HPO (search, pruning, distributed trials)

| Tool | Typical usage | Notable features | License | Stars |
|------|--------------|------------------|---------|-------|
| Optuna | define-by-run HPO | samplers + pruning, parallel studies | MIT | ~13.5k |

**Minimal Optuna idea:**
```
def objective(trial):
    lr = trial.suggest_float("lr", 1e-5, 1e-2, log=True)
    return train_eval(lr)

study = optuna.create_study(direction="minimize")
study.optimize(objective, n_trials=50)
```

---

## Design Decision

**Architecture: Local-first** (`.exp/` folder, no server, optional UI later) -- like DVC/Aim.

### Core philosophy

- Local-first core (always works offline) + optional server/UI later
- Reproducibility by construction:
  - Config snapshot is immutable per run
  - Deterministic run ID = hash(config + code version + data refs)
  - Artifacts are content-addressed (DVC-like)

### Storage model

- Event log + index
  - Append-only: `.exp/runs/<run_id>/events.bin` (or SDN-lines)
  - Periodic index: `.exp/index.sqlite` (fast queries, UI later)
- Artifacts:
  - `.exp/cache/sha256/<...>` (blobs)
  - `.exp/runs/<run_id>/artifacts.sdn` (refs)

### Config system features (from Hydra/OmegaConf)

- Composition: `model=resnet` selects `configs/model/resnet.sdn`
- Override grammar: `trainer.max_epochs=50`
- Interpolation: `${env:CUDA_VISIBLE_DEVICES}` and `${config:paths.data}`
- Locking: once a run starts, config becomes read-only + hashed

### Sweeps (Optuna-inspired)

- Study = optimization campaign
- Trial = one training run attempt
- `trial.suggest_*()` = define-by-run search space
- Pruner = early stop unpromising trials
- Extras: retries, artifact-aware objectives, budget scheduling

### Lightning integration

- `SimpleLogger` (Lightning logger): forwards metrics/hparams
- `SimpleCheckpointIO` (optional): logs checkpoints as artifacts
- `SimpleSweepCallback` (optional): reads suggested params from sweep engine
