# Experiment Tracking (W&B-like)

**Status:** Planned
**Target:** Simple 0.x
**Dependencies:** Config system, file I/O, async operations
**Tracking:** Feature DB #TBD

---

## Overview

A comprehensive experiment tracking system inspired by Weights & Biases (W&B), designed for Simple ML workflows. Provides local-first logging with optional remote synchronization, artifact versioning, hyperparameter sweeps, and rich media support.

### Design Goals

1. **Local-first** - All data stored locally, sync optional
2. **Offline mode** - Full functionality without network
3. **Lineage tracking** - Dataset/model provenance
4. **Rich media** - Images, videos, audio, HTML
5. **Structured logging** - Tables with typed columns
6. **Hyperparameter sweeps** - Bayesian/grid/random search
7. **Simple integration** - Context manager API

---

## Core Features

### 1. Run Lifecycle

**Basic Usage:**
```simple
import Track from ml.tracking

# Initialize run
with Track.run(
    project="image-classification",
    name="resnet50-exp1",  # Optional
    config=cfg,
    tags=["baseline", "resnet"]
) as run:
    # Training loop
    for epoch in 0..num_epochs:
        loss = train_epoch(model, dataloader)
        acc = evaluate(model, val_loader)

        # Log metrics
        run.log({
            "train/loss": loss,
            "train/acc": acc,
            "epoch": epoch
        }, step=epoch)

# Auto-cleanup on exit
```

**Run Properties:**
```simple
run.id            # Unique run ID (e.g., "abc123def")
run.name          # Human-readable name
run.project       # Project name
run.dir           # Local directory (.simple/runs/{project}/{run_id}/)
run.config        # Configuration dict
run.summary       # Final metrics summary
run.tags          # List of tags
run.start_time    # Run start timestamp
run.end_time      # Run end timestamp (null if running)
```

### 2. Metric Logging

**Scalar Logging:**
```simple
# Single metric
run.log({"loss": 0.5}, step=100)

# Multiple metrics
run.log({
    "train/loss": 0.45,
    "train/acc": 0.92,
    "val/loss": 0.52,
    "val/acc": 0.89,
    "lr": 1e-3
}, step=100)

# Auto-incrementing step
run.log({"loss": 0.5})  # step = last_step + 1
```

**Histogram Logging:**
```simple
# Log distribution of values
run.log_histogram("gradients/layer1", gradients, step=step)
run.log_histogram("activations/relu2", activations, bins=50)
```

**Custom Plots:**
```simple
# Line plot
run.log_plot(
    "metrics",
    x=[0, 1, 2, 3],
    y=[0.1, 0.3, 0.5, 0.8],
    title="Training Progress"
)

# Scatter plot
run.log_scatter("embeddings", points_2d, labels=labels)
```

### 3. Offline Mode

**Configuration:**
```simple
# Set mode before run
Track.set_mode("offline")  # or "online"

with Track.run(project="test") as run:
    run.log({"loss": 0.5})
# Logged to local storage only

# Later, sync to server
Track.sync(run.dir)  # Sync specific run
Track.sync_all()     # Sync all offline runs
```

**Mode Options:**
- `online` - Real-time sync to remote server
- `offline` - Local storage only
- `disabled` - No-op for all operations (testing)

### 4. Model Watching (Gradients/Parameters)

**Auto-logging:**
```simple
import torch from ml.torch

model = ResNet50()
optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)

# Watch model
run.watch(
    model,
    log="gradients",      # "gradients" | "parameters" | "all"
    log_freq=100,         # Log every N steps
    log_graph=true        # Log computation graph
)

# Training loop - gradients logged automatically
for batch in dataloader:
    loss = forward_pass(model, batch)
    loss.backward()
    optimizer.step()      # Gradients logged here
    run.log({"loss": loss.item()})
```

**Manual Gradient Logging:**
```simple
# Log specific parameters
for name, param in model.named_parameters():
    if param.grad is not null:
        run.log_histogram(f"grad/{name}", param.grad, step=step)
        run.log({f"grad_norm/{name}": param.grad.norm().item()}, step=step)
```

### 5. Artifacts & Lineage

**Dataset Artifacts:**
```simple
# Create and log dataset
dataset = Track.Artifact(
    name="imagenet-100",
    type="dataset",
    description="ImageNet subset with 100 classes"
)

# Add files
dataset.add_file("data/train.tar.gz")
dataset.add_file("data/val.tar.gz")
dataset.add_dir("data/metadata/")

# Mark as input (for lineage)
run.use_artifact(dataset)

# Access files
dataset_path = dataset.download()  # Returns local path
```

**Model Artifacts:**
```simple
# Save trained model
model_artifact = Track.Artifact(
    name="resnet50-imagenet",
    type="model",
    metadata={
        "architecture": "ResNet50",
        "input_size": [3, 224, 224],
        "num_classes": 1000
    }
)

# Add checkpoint
torch.save(model.state_dict(), "checkpoint.pt")
model_artifact.add_file("checkpoint.pt")
model_artifact.add_file("config.sdn")

# Log as output
run.log_artifact(model_artifact)
```

**Versioning:**
```simple
# Artifacts are automatically versioned
# v0, v1, v2, ...

# Use specific version
dataset = run.use_artifact("imagenet-100:v2")

# Use alias
dataset = run.use_artifact("imagenet-100:latest")
dataset = run.use_artifact("imagenet-100:production")
```

### 6. Registry (Governance & Lineage)

**Publishing to Registry:**
```simple
# Publish artifact to shared registry
Track.Registry.publish(
    collection="Datasets/ImageNet",
    artifact=dataset_artifact,
    alias="v1",
    description="ImageNet 2012 training set"
)

# Use from registry
dataset = Track.Registry.get("Datasets/ImageNet:v1")
run.use_artifact(dataset)
```

**Lineage Tracking:**
```simple
# Automatic lineage graph
# dataset (v1) -> [run_1, run_2] -> model (v1) -> [run_3] -> model (v2)

# Query lineage
lineage = Track.Registry.lineage(artifact="model-v2")
# Returns: {
#   "inputs": ["dataset-v1"],
#   "runs": ["run_1", "run_2", "run_3"],
#   "outputs": ["model-v1", "model-v2"]
# }
```

### 7. Hyperparameter Sweeps

**Define Sweep:**
```simple
# Create sweep configuration
sweep_config = Track.Sweep.define(
    method="bayes",  # "bayes" | "grid" | "random"
    metric={
        "name": "val/loss",
        "goal": "minimize"
    },
    parameters={
        "lr": Track.Sweep.LogUniform(1e-5, 1e-2),
        "batch_size": Track.Sweep.Choice([32, 64, 128, 256]),
        "optimizer": Track.Sweep.Choice(["adam", "sgd", "adamw"]),
        "dropout": Track.Sweep.Uniform(0.0, 0.5),
        "weight_decay": Track.Sweep.LogUniform(1e-6, 1e-3)
    },
    early_terminate={
        "type": "hyperband",
        "min_iter": 3
    }
)

# Create sweep
sweep_id = Track.Sweep.create(sweep_config, project="image-classification")
```

**Run Sweep:**
```simple
# Define training function
fn train(cfg: {str: any}):
    with Track.run(config=cfg) as run:
        model = create_model(cfg)

        for epoch in 0..cfg["epochs"]:
            loss = train_epoch(model, cfg)
            acc = validate(model)

            run.log({
                "train/loss": loss,
                "val/acc": acc
            }, step=epoch)

# Launch sweep agent
Track.Sweep.agent(
    sweep_id,
    function=train,
    count=20  # Run 20 experiments
)
```

**Parallel Sweeps:**
```simple
# Launch multiple agents in parallel
# Agent 1 (terminal 1)
Track.Sweep.agent(sweep_id, function=train, count=10)

# Agent 2 (terminal 2)
Track.Sweep.agent(sweep_id, function=train, count=10)

# Agent 3 (terminal 3)
Track.Sweep.agent(sweep_id, function=train, count=10)

# Centralized controller distributes work
```

### 8. Tables (Structured Data)

**Create Tables:**
```simple
# Define table with typed columns
predictions_table = Track.Table(
    columns=["id", "image", "pred", "label", "confidence", "correct"]
)

# Add rows
for i, (img, pred, label) in enumerate(results):
    predictions_table.add_row([
        i,
        Track.Media.image(img),  # Rich media
        pred,
        label,
        confidence[i],
        pred == label
    ])

# Log table
run.log({"predictions": predictions_table}, step=epoch)
```

**Query Tables:**
```simple
# Load table from run
table = run.table("predictions")

# Filter
correct_preds = table.filter(lambda row: row["correct"] == true)

# Aggregate
avg_confidence = table.mean("confidence")
accuracy = table.count(lambda r: r["correct"]) / table.len()
```

### 9. Media Logging

**Images:**
```simple
# Single image
run.log_image("sample", img_tensor, caption="Input image", step=step)

# Multiple images
run.log_images("gallery", [img1, img2, img3], captions=["a", "b", "c"])

# Image with masks/boxes
run.log_image("segmentation", img, masks=[mask1, mask2], step=step)
run.log_image("detection", img, boxes=[
    {"box": [10, 20, 100, 200], "label": "cat", "score": 0.95}
], step=step)
```

**Video:**
```simple
# Video tensor (T, C, H, W)
run.log_video("training_progress", video_tensor, fps=30, step=step)
```

**Audio:**
```simple
# Audio tensor (samples,) or (channels, samples)
run.log_audio("speech", audio_tensor, sample_rate=16000, step=step)
```

**HTML:**
```simple
# Custom visualizations
html_content = """
<div style="background: #f0f0f0; padding: 20px;">
    <h2>Model Analysis</h2>
    <p>Accuracy: 92.5%</p>
</div>
"""
run.log_html("analysis", html_content)
```

**3D Objects:**
```simple
# Point clouds, meshes
run.log_point_cloud("scene", points, colors=colors)
run.log_mesh("model_3d", vertices, faces)
```

---

## API Reference

### Run Management

```simple
# Create run
Track.run(
    project: Str,
    name: Str = null,              # Auto-generated if null
    config: {str: any} = {},
    tags: [Str] = [],
    notes: Str = "",
    dir: Str = null,               # Custom run directory
    resume: Str | Bool = false,    # Resume run by ID or "allow"
    reinit: Bool = false           # Reinitialize existing run
) -> Run

# Run methods
run.log(metrics: {str: any}, step: Int = null)
run.log_histogram(name: Str, values: Tensor, bins: Int = 64, step: Int = null)
run.log_image(name: Str, image: Tensor, caption: Str = "", step: Int = null)
run.log_video(name: Str, video: Tensor, fps: Int = 30, step: Int = null)
run.log_audio(name: Str, audio: Tensor, sample_rate: Int, step: Int = null)
run.log_html(name: Str, html: Str)
run.summary.update(summary: {str: any})
run.finish()

# Model watching
run.watch(
    model: torch.nn.Module,
    log: Str = "gradients",        # "gradients" | "parameters" | "all"
    log_freq: Int = 100,
    log_graph: Bool = false
)
run.unwatch(model: torch.nn.Module = null)  # null = unwatch all
```

### Artifacts

```simple
# Create artifact
Track.Artifact(
    name: Str,
    type: Str,                     # "dataset" | "model" | "result" | custom
    description: Str = "",
    metadata: {str: any} = {}
)

# Artifact methods
artifact.add_file(path: Str, name: Str = null)
artifact.add_dir(path: Str, name: Str = null)
artifact.add_reference(uri: Str, name: Str = null)  # External URL
artifact.download() -> Str                          # Returns local path
artifact.checkout(version: Str = "latest") -> Str

# Use artifacts
run.use_artifact(artifact: Artifact | Str) -> Artifact
run.log_artifact(artifact: Artifact, aliases: [Str] = [])
```

### Registry

```simple
# Publish
Track.Registry.publish(
    collection: Str,               # "Models/ResNet" or "Datasets/ImageNet"
    artifact: Artifact,
    alias: Str = "latest",
    description: Str = ""
)

# Retrieve
Track.Registry.get(path: Str) -> Artifact  # "Models/ResNet:v1"
Track.Registry.list(collection: Str) -> [Artifact]

# Lineage
Track.Registry.lineage(artifact: Str) -> {str: any}
Track.Registry.dependencies(artifact: Str) -> [Artifact]
Track.Registry.dependents(artifact: Str) -> [Artifact]
```

### Sweeps

```simple
# Distribution types
Track.Sweep.Uniform(min: F64, max: F64)
Track.Sweep.LogUniform(min: F64, max: F64)
Track.Sweep.Normal(mu: F64, sigma: F64)
Track.Sweep.Choice(values: [any])
Track.Sweep.IntUniform(min: Int, max: Int)

# Define sweep
Track.Sweep.define(
    method: Str,                   # "bayes" | "grid" | "random"
    metric: {name: Str, goal: Str},  # goal: "minimize" | "maximize"
    parameters: {str: Distribution},
    early_terminate: {type: Str, ...} = null
) -> {str: any}

# Create and run
Track.Sweep.create(config: {str: any}, project: Str) -> Str
Track.Sweep.agent(sweep_id: Str, function: Fn, count: Int = null)

# Query sweeps
Track.Sweep.get(sweep_id: Str) -> Sweep
Track.Sweep.stop(sweep_id: Str)
```

### Tables

```simple
# Create table
Track.Table(
    columns: [Str],
    data: [[any]] = []
)

# Methods
table.add_row(row: [any])
table.add_rows(rows: [[any]])
table.get_column(name: Str) -> [any]
table.filter(predicate: Fn) -> Table
table.map(transform: Fn) -> Table
table.len() -> Int
```

### Media

```simple
Track.Media.image(tensor: Tensor, caption: Str = "") -> Image
Track.Media.video(tensor: Tensor, fps: Int = 30) -> Video
Track.Media.audio(tensor: Tensor, sample_rate: Int) -> Audio
Track.Media.html(content: Str) -> Html
Track.Media.plot(data: {str: any}, type: Str) -> Plot
```

### Configuration

```simple
# Global settings
Track.set_mode(mode: Str)          # "online" | "offline" | "disabled"
Track.set_dir(path: Str)           # Root directory for runs
Track.login(api_key: Str = null, host: Str = null)
Track.sync(run_dir: Str)           # Sync specific run
Track.sync_all()                    # Sync all offline runs
```

---

## Storage Format

### Directory Structure

```
.simple/
└── runs/
    └── {project}/
        └── {run_id}/
            ├── metadata.sdn           # Run config and metadata
            ├── metrics.jsonl          # Time-series metrics
            ├── history.jsonl          # Full event log
            ├── summary.sdn            # Final summary
            ├── artifacts/             # Logged artifacts
            │   ├── model-v1/
            │   └── dataset-v1/
            ├── media/                 # Images, videos, etc.
            │   ├── images/
            │   ├── videos/
            │   └── audio/
            ├── tables/                # Table data
            │   └── predictions.parquet
            └── files/                 # Uploaded files
```

### Metadata Format (SDN)

```sdn
# metadata.sdn
id = abc123def
name = resnet50-exp1
project = image-classification
tags = [baseline, resnet]
created_at = 2026-01-10T15:30:00Z
finished_at = 2026-01-10T18:45:00Z

config:
    model:
        type = resnet50
        pretrained = true
    train:
        epochs = 50
        lr = 1e-3
        batch_size = 64

system:
    hostname = gpu-server-01
    platform = linux
    python_version = 3.11.5
    gpu = NVIDIA A100 40GB
```

### Metrics Format (JSONL)

```jsonl
{"step": 0, "train/loss": 2.304, "train/acc": 0.125, "timestamp": 1704902400.123}
{"step": 1, "train/loss": 2.156, "train/acc": 0.234, "timestamp": 1704902410.456}
{"step": 2, "train/loss": 1.987, "train/acc": 0.345, "timestamp": 1704902420.789}
```

---

## Integration with Existing Infrastructure

### File I/O & Async Operations

Uses existing infrastructure from `src/runtime/src/value/file_io/`:
```simple
# Async artifact download
artifact_handle = native_async_file_create(artifact_path, mode=0, prefault=true)
native_async_file_start_loading(artifact_handle)

# Background tokenizer loading
tokenizer_handle = load_tokenizer_async(vocab_path)
# Continue training, tokenizer loads in parallel
```

### Mmap for Large Artifacts

```simple
# Zero-copy artifact access
artifact_region = native_mmap_create(artifact_path)
data = native_mmap_read(artifact_region, offset=0, size=file_size)

# Shared memory for multi-process
shared_region = native_mmap_create_shared(path, size)
```

### Background Sync

```simple
# Non-blocking sync to remote
sync_handle = Track._async_sync(run_dir)

# Continue training while syncing
for batch in dataloader:
    loss = train_step(batch)
    run.log({"loss": loss})

# Check sync status
if Track._sync_ready(sync_handle):
    print("Sync complete")
```

---

## Usage Examples

### Example 1: Image Classification

```simple
import Track from ml.tracking
import Conf from config
import torch from ml.torch

# Load config
cfg = Conf.load_sdn("config.sdn")

# Initialize tracking
with Track.run(project="cifar10", config=Conf.to_dict(cfg)) as run:
    # Load dataset
    train_ds = torch.data.CIFAR10(root="./data", train=true)
    val_ds = torch.data.CIFAR10(root="./data", train=false)

    train_loader = torch.data.DataLoader(train_ds, batch_size=cfg.batch_size)
    val_loader = torch.data.DataLoader(val_ds, batch_size=cfg.batch_size)

    # Create model
    model = ResNet50(num_classes=10)
    optimizer = torch.optim.Adam(model.parameters(), lr=cfg.lr)

    # Watch model
    run.watch(model, log="gradients", log_freq=100)

    # Training loop
    for epoch in 0..cfg.epochs:
        # Train
        model.train()
        train_loss = 0.0

        for batch in train_loader:
            images, labels = batch
            pred = model(images)
            loss = F.cross_entropy(pred, labels)

            loss.backward()
            optimizer.step()
            optimizer.zero_grad()

            train_loss += loss.item()

        # Validate
        model.eval()
        val_loss, val_acc = evaluate(model, val_loader)

        # Log metrics
        run.log({
            "train/loss": train_loss / len(train_loader),
            "val/loss": val_loss,
            "val/acc": val_acc,
            "epoch": epoch
        }, step=epoch)

        # Log sample predictions
        if epoch % 5 == 0:
            sample_images, sample_labels, predictions = predict_samples(model, val_loader, n=16)
            run.log_images("predictions", sample_images, captions=[
                f"True: {sample_labels[i]}, Pred: {predictions[i]}"
                for i in 0..16
            ], step=epoch)

    # Save model
    model_artifact = Track.Artifact("cifar10-resnet50", type="model")
    torch.save(model.state_dict(), "model.pt")
    model_artifact.add_file("model.pt")
    run.log_artifact(model_artifact, aliases=["latest", f"epoch-{cfg.epochs}"])
```

### Example 2: Hyperparameter Sweep

```simple
# Define sweep
sweep_config = Track.Sweep.define(
    method="bayes",
    metric={"name": "val/acc", "goal": "maximize"},
    parameters={
        "lr": Track.Sweep.LogUniform(1e-5, 1e-2),
        "batch_size": Track.Sweep.Choice([32, 64, 128]),
        "dropout": Track.Sweep.Uniform(0.0, 0.5),
        "weight_decay": Track.Sweep.LogUniform(1e-6, 1e-3)
    }
)

sweep_id = Track.Sweep.create(sweep_config, project="cifar10-sweep")

# Training function
fn train_sweep(cfg: {str: any}):
    with Track.run(config=cfg) as run:
        model = create_model(cfg["dropout"])
        optimizer = create_optimizer(model, cfg["lr"], cfg["weight_decay"])

        for epoch in 0..30:
            train_loss = train_epoch(model, optimizer, cfg["batch_size"])
            val_acc = validate(model, cfg["batch_size"])

            run.log({
                "train/loss": train_loss,
                "val/acc": val_acc
            }, step=epoch)

# Run sweep
Track.Sweep.agent(sweep_id, function=train_sweep, count=50)
```

---

## Testing Strategy

```simple
# test/unit/tracking/run_spec.spl
feature "Experiment Tracking":
    scenario "Create and log to run":
        with Track.run(project="test") as run:
            assert run.id is not null
            assert run.project == "test"

            run.log({"loss": 0.5}, step=0)
            run.log({"loss": 0.3}, step=1)

        # Verify log file
        metrics = read_jsonl(f"{run.dir}/metrics.jsonl")
        assert len(metrics) == 2
        assert metrics[0]["loss"] == 0.5

    scenario "Offline mode":
        Track.set_mode("offline")

        with Track.run(project="test") as run:
            run.log({"loss": 0.5})

        # Verify no network calls made
        assert not network_activity_detected()

    scenario "Artifact logging":
        with Track.run(project="test") as run:
            artifact = Track.Artifact("test-data", type="dataset")
            artifact.add_file("test.txt")
            run.log_artifact(artifact)

        # Verify artifact stored
        assert exists(f"{run.dir}/artifacts/test-data/")
```

---

## Implementation Roadmap

### Phase 1: Core (v0.1)
- [ ] Run lifecycle management
- [ ] Local storage (JSONL metrics)
- [ ] Basic logging (scalars, histograms)
- [ ] Offline mode
- [ ] SDN metadata format

### Phase 2: Rich Media (v0.2)
- [ ] Image logging
- [ ] Video logging
- [ ] Audio logging
- [ ] Table support
- [ ] HTML logging

### Phase 3: Artifacts (v0.3)
- [ ] Artifact creation and versioning
- [ ] Lineage tracking
- [ ] Registry system
- [ ] Artifact download/cache

### Phase 4: Sweeps (v0.4)
- [ ] Sweep definition
- [ ] Bayesian optimization
- [ ] Grid/random search
- [ ] Early termination (Hyperband)
- [ ] Multi-agent parallelization

### Phase 5: Advanced (v0.5)
- [ ] Model watching (gradients/parameters)
- [ ] Computation graph logging
- [ ] Remote sync
- [ ] Web UI for visualization
- [ ] Report generation

---

## References

- W&B Docs: https://docs.wandb.ai/
- MLflow: https://mlflow.org/
- TensorBoard: https://www.tensorflow.org/tensorboard
- Feature tracking: `doc/feature/feature_db.sdn`
