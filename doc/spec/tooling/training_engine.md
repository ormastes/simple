# Training Engine (PyTorch Ignite-like)

**Status:** Planned
**Target:** Simple 0.x
**Dependencies:** torch module, tracking system
**Tracking:** Feature DB #TBD

---

## Overview

A flexible, event-driven training engine inspired by PyTorch Ignite. Provides composable training loops with extensible event handlers, metrics computation, checkpointing, and early stopping. Designed to eliminate boilerplate while maintaining full control over the training process.

### Design Goals

1. **Event-driven** - Hook into any point in training lifecycle
2. **Composable** - Mix and match handlers
3. **Flexible** - Support arbitrary training logic
4. **Reusable** - Share handlers across projects
5. **Distributed-ready** - Multi-GPU support
6. **Minimal boilerplate** - Focus on model logic

---

## Core Concepts

### 1. Engine

The `Engine` is a generic training/evaluation loop executor:

**Basic Structure:**
```simple
import Engine, Events from ml.engine

# Define process function
fn train_step(engine: Engine, batch: any) -> any:
    model.train()
    optimizer.zero_grad()

    x, y = batch
    pred = model(x)
    loss = loss_fn(pred, y)

    loss.backward()
    optimizer.step()

    return {"loss": loss.item()}

# Create engine
trainer = Engine(train_step)

# Run engine
trainer.run(train_loader, max_epochs=10)
```

**Engine State:**
```simple
engine.state.epoch            # Current epoch (0-indexed)
engine.state.iteration        # Global iteration counter
engine.state.epoch_iteration  # Iteration within current epoch
engine.state.max_epochs       # Total epochs to run
engine.state.output           # Return value of process function
engine.state.metrics          # Computed metrics dict
engine.state.dataloader       # Current dataloader
engine.state.batch            # Current batch
```

### 2. Events

Built-in lifecycle events:

```simple
Events.STARTED                    # Engine started
Events.EPOCH_STARTED              # Epoch started
Events.ITERATION_STARTED          # Before batch processing
Events.ITERATION_COMPLETED        # After batch processing
Events.EPOCH_COMPLETED            # Epoch completed
Events.COMPLETED                  # Engine completed all epochs
Events.EXCEPTION_RAISED           # Exception during execution

# Periodic events
Events.ITERATION_COMPLETED(every=100)      # Every 100 iterations
Events.EPOCH_COMPLETED(every=5)            # Every 5 epochs
Events.ITERATION_COMPLETED(once=1000)      # Once at iteration 1000
```

### 3. Event Handlers

**Attaching Handlers:**
```simple
# Simple handler
@trainer.on(Events.EPOCH_COMPLETED)
fn log_metrics(engine: Engine):
    print(f"Epoch {engine.state.epoch}: loss={engine.state.metrics['loss']}")

# Alternative syntax
fn log_metrics(engine: Engine):
    print(f"Epoch {engine.state.epoch}: loss={engine.state.metrics['loss']}")

trainer.on(Events.EPOCH_COMPLETED, log_metrics)

# Periodic handler
@trainer.on(Events.ITERATION_COMPLETED(every=100))
fn log_batch(engine: Engine):
    print(f"Iter {engine.state.iteration}: loss={engine.state.output['loss']}")
```

**Handler Order:**
```simple
# Handlers execute in registration order
trainer.on(Events.EPOCH_COMPLETED, handler1)  # Runs first
trainer.on(Events.EPOCH_COMPLETED, handler2)  # Runs second
trainer.on(Events.EPOCH_COMPLETED, handler3)  # Runs third

# Priority control (optional)
trainer.on(Events.EPOCH_COMPLETED, handler_urgent, priority=10)   # High priority
trainer.on(Events.EPOCH_COMPLETED, handler_normal, priority=0)    # Default
trainer.on(Events.EPOCH_COMPLETED, handler_late, priority=-10)    # Low priority
```

### 4. Custom Events

**Define and Fire:**
```simple
# Define custom events
enum TrainEvents:
    BACKWARD_STARTED = "backward_started"
    BACKWARD_COMPLETED = "backward_completed"
    OPTIMIZER_STEP = "optimizer_step"

# Register events
trainer.register_events(TrainEvents)

# Fire events in process function
fn train_step(engine: Engine, batch: any):
    x, y = batch
    pred = model(x)
    loss = loss_fn(pred, y)

    engine.fire_event(TrainEvents.BACKWARD_STARTED)
    loss.backward()
    engine.fire_event(TrainEvents.BACKWARD_COMPLETED)

    engine.fire_event(TrainEvents.OPTIMIZER_STEP)
    optimizer.step()

    return {"loss": loss.item()}

# Attach custom event handlers
@trainer.on(TrainEvents.BACKWARD_COMPLETED)
fn clip_gradients(engine: Engine):
    torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
```

---

## Metrics

### 1. Metric Interface

```simple
# Base metric class
class Metric:
    fn reset(self):
        # Reset internal state for new epoch
        pass

    fn update(self, output: any):
        # Accumulate from batch output
        pass

    fn compute(self) -> F64:
        # Compute final metric value
        pass
```

### 2. Built-in Metrics

**Classification Metrics:**
```simple
from ml.engine.metrics import Accuracy, Precision, Recall, F1Score

# Attach metric to engine
accuracy = Accuracy()
trainer.add_metric(accuracy, "acc")

# Metrics auto-compute on Events.EPOCH_COMPLETED
@trainer.on(Events.EPOCH_COMPLETED)
fn log_accuracy(engine: Engine):
    print(f"Accuracy: {engine.state.metrics['acc']:.4f}")
```

**Regression Metrics:**
```simple
from ml.engine.metrics import MSE, MAE, R2Score

mse = MSE()
mae = MAE()
trainer.add_metrics({
    "mse": mse,
    "mae": mae
})
```

**Custom Metrics:**
```simple
class PerplexityMetric(Metric):
    fn __init__(self):
        self.total_loss = 0.0
        self.count = 0

    fn reset(self):
        self.total_loss = 0.0
        self.count = 0

    fn update(self, output: any):
        self.total_loss += output["loss"]
        self.count += 1

    fn compute(self) -> F64:
        avg_loss = self.total_loss / self.count
        return exp(avg_loss)

perplexity = PerplexityMetric()
trainer.add_metric(perplexity, "ppl")
```

### 3. Distributed Metrics

```simple
from ml.engine.metrics import DistributedMetric

# Automatic reduction across GPUs
accuracy = DistributedMetric(
    base_metric=Accuracy(),
    reduce_op="mean",      # "sum" | "mean" | "max" | "min"
    device="cuda"
)

trainer.add_metric(accuracy, "acc")
```

---

## Built-in Handlers

### 1. Checkpoint Handler

```simple
from ml.engine.handlers import Checkpoint

# Save model and optimizer state
checkpoint = Checkpoint(
    to_save={
        "model": model,
        "optimizer": optimizer,
        "trainer": trainer  # Save engine state
    },
    save_dir="checkpoints",
    filename_prefix="best",
    n_saved=3,              # Keep last 3 checkpoints
    global_step_transform=lambda engine, event: engine.state.iteration
)

# Save every 1000 iterations
trainer.on(Events.ITERATION_COMPLETED(every=1000), checkpoint)

# Save best model based on metric
best_checkpoint = Checkpoint(
    to_save={"model": model},
    save_dir="checkpoints",
    filename_prefix="best",
    score_function=lambda engine: engine.state.metrics["acc"],
    score_name="acc",
    n_saved=1
)
trainer.on(Events.EPOCH_COMPLETED, best_checkpoint)
```

### 2. Early Stopping

```simple
from ml.engine.handlers import EarlyStopping

# Stop if val loss doesn't improve
early_stop = EarlyStopping(
    patience=10,
    min_delta=0.001,
    score_function=lambda engine: -engine.state.metrics["val_loss"],  # Maximize
    trainer=trainer  # Engine to stop
)

evaluator.on(Events.EPOCH_COMPLETED, early_stop)
```

### 3. Learning Rate Scheduler

```simple
from ml.engine.handlers import LRScheduler

# Step LR
scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=10, gamma=0.1)
lr_handler = LRScheduler(scheduler)
trainer.on(Events.EPOCH_COMPLETED, lr_handler)

# ReduceLROnPlateau (metric-based)
scheduler = torch.optim.lr_scheduler.ReduceLROnPlateau(
    optimizer, mode="min", patience=5
)
lr_handler = LRScheduler(scheduler, metric_name="val_loss")
evaluator.on(Events.EPOCH_COMPLETED, lr_handler)
```

### 4. Timer

```simple
from ml.engine.handlers import Timer

timer = Timer()
timer.attach(trainer, start=Events.STARTED, step=Events.ITERATION_COMPLETED)

@trainer.on(Events.EPOCH_COMPLETED)
fn log_time(engine: Engine):
    print(f"Epoch time: {timer.value():.2f}s")
    print(f"Average batch time: {timer.step_time():.4f}s")
```

### 5. Progress Bar

```simple
from ml.engine.handlers import ProgressBar

pbar = ProgressBar()
pbar.attach(trainer, metric_names=["loss"], output_transform=lambda x: x)

# Output:
# Epoch [1/10]: 100%|██████████| 1000/1000 [01:23<00:00, 12.01it/s, loss=0.345]
```

### 6. Tracking Integration

```simple
from ml.engine.handlers import TrackingHandler

# Log to Track system
tracking_handler = TrackingHandler(
    run=run,
    metric_names=["loss", "acc"],
    output_transform=lambda x: x,
    global_step_transform=lambda engine, event: engine.state.iteration
)

trainer.on(Events.ITERATION_COMPLETED(every=10), tracking_handler)
```

---

## Complete Training Example

```simple
import torch from ml.torch
import Engine, Events from ml.engine
import Checkpoint, EarlyStopping, ProgressBar from ml.engine.handlers
import Accuracy from ml.engine.metrics
import Track from ml.tracking
import Conf from config

# Load config
cfg = Conf.load_sdn("config/train.sdn")

# Create model
model = ResNet50(num_classes=10)
optimizer = torch.optim.Adam(model.parameters(), lr=cfg.lr)
loss_fn = torch.nn.CrossEntropyLoss()

# Create data loaders
train_loader = create_dataloader(cfg, split="train")
val_loader = create_dataloader(cfg, split="val")

# Define training step
fn train_step(engine: Engine, batch: any):
    model.train()
    optimizer.zero_grad()

    images, labels = batch
    pred = model(images)
    loss = loss_fn(pred, labels)

    loss.backward()
    optimizer.step()

    return {
        "loss": loss.item(),
        "pred": pred.detach(),
        "labels": labels
    }

# Define validation step
fn val_step(engine: Engine, batch: any):
    model.eval()

    with torch.no_grad():
        images, labels = batch
        pred = model(images)
        loss = loss_fn(pred, labels)

    return {
        "loss": loss.item(),
        "pred": pred,
        "labels": labels
    }

# Create engines
trainer = Engine(train_step)
evaluator = Engine(val_step)

# Add metrics to evaluator
accuracy = Accuracy(output_transform=lambda x: (x["pred"], x["labels"]))
evaluator.add_metrics({
    "acc": accuracy,
    "loss": Loss(loss_fn, output_transform=lambda x: (x["pred"], x["labels"]))
})

# Setup tracking
with Track.run(project="cifar10", config=Conf.to_dict(cfg)) as run:
    # Progress bar
    pbar = ProgressBar()
    pbar.attach(trainer, output_transform=lambda x: {"loss": x["loss"]})

    # Run validation every epoch
    @trainer.on(Events.EPOCH_COMPLETED)
    fn run_validation(engine: Engine):
        evaluator.run(val_loader)
        metrics = evaluator.state.metrics

        # Log to tracking
        run.log({
            "train/loss": engine.state.output["loss"],
            "val/loss": metrics["loss"],
            "val/acc": metrics["acc"],
            "epoch": engine.state.epoch
        }, step=engine.state.epoch)

        print(f"Epoch {engine.state.epoch}")
        print(f"  Train Loss: {engine.state.output['loss']:.4f}")
        print(f"  Val Loss: {metrics['loss']:.4f}")
        print(f"  Val Acc: {metrics['acc']:.4f}")

    # Checkpoint best model
    best_checkpoint = Checkpoint(
        to_save={"model": model, "optimizer": optimizer},
        save_dir=cfg.checkpoint_dir,
        filename_prefix="best",
        score_function=lambda eng: evaluator.state.metrics["acc"],
        score_name="acc",
        n_saved=1
    )
    trainer.on(Events.EPOCH_COMPLETED, best_checkpoint)

    # Early stopping
    early_stop = EarlyStopping(
        patience=cfg.patience,
        score_function=lambda eng: evaluator.state.metrics["acc"],
        trainer=trainer
    )
    evaluator.on(Events.EPOCH_COMPLETED, early_stop)

    # Learning rate scheduling
    scheduler = torch.optim.lr_scheduler.ReduceLROnPlateau(
        optimizer, mode="max", patience=5
    )
    lr_handler = LRScheduler(
        scheduler,
        metric_name="acc",
        metric_engine=evaluator
    )
    trainer.on(Events.EPOCH_COMPLETED, lr_handler)

    # Run training
    trainer.run(train_loader, max_epochs=cfg.epochs)

    # Save final model
    final_artifact = Track.Artifact("cifar10-resnet50", type="model")
    torch.save(model.state_dict(), "final_model.pt")
    final_artifact.add_file("final_model.pt")
    run.log_artifact(final_artifact, aliases=["final"])

print("Training completed!")
```

---

## Advanced Features

### 1. Multiple Engines

```simple
# Train on source domain
source_trainer = Engine(train_step_source)

# Train on target domain
target_trainer = Engine(train_step_target)

# Alternate training
for epoch in 0..num_epochs:
    source_trainer.run(source_loader, max_epochs=1)
    target_trainer.run(target_loader, max_epochs=1)

    # Evaluate
    evaluator.run(val_loader)
```

### 2. Engine Composition

```simple
# Run evaluator at specific iterations
@trainer.on(Events.ITERATION_COMPLETED(every=500))
fn evaluate_during_training(engine: Engine):
    evaluator.run(val_loader)
    val_acc = evaluator.state.metrics["acc"]

    if val_acc > best_acc:
        save_checkpoint(model, f"checkpoint_iter_{engine.state.iteration}.pt")
```

### 3. State Serialization

```simple
# Save engine state
checkpoint = Checkpoint(
    to_save={"trainer": trainer},
    save_dir="checkpoints"
)
trainer.on(Events.ITERATION_COMPLETED(every=1000), checkpoint)

# Resume training
state_dict = torch.load("checkpoints/checkpoint_5000.pt")
trainer.load_state_dict(state_dict["trainer"])
trainer.run(train_loader, max_epochs=100)  # Resumes from iteration 5000
```

### 4. Distributed Training

```simple
import DistributedDataParallel, DistributedSampler from ml.torch.distributed

# Setup distributed
model = DistributedDataParallel(model, device_ids=[local_rank])
train_sampler = DistributedSampler(train_dataset, num_replicas=world_size, rank=rank)
train_loader = DataLoader(train_dataset, sampler=train_sampler, ...)

# Create engine (same as before)
trainer = Engine(train_step)

# Distributed metrics
from ml.engine.metrics import DistributedAccuracy

accuracy = DistributedAccuracy(device=device)
evaluator.add_metric(accuracy, "acc")

# Run (automatic synchronization)
trainer.run(train_loader, max_epochs=10)
```

---

## API Reference

### Engine

```simple
class Engine:
    fn __init__(self, process_function: Fn)

    # Event management
    fn on(self, event: Event, handler: Fn, priority: Int = 0)
    fn register_events(self, *events: Event)
    fn fire_event(self, event: Event)

    # Metrics
    fn add_metric(self, metric: Metric, name: Str)
    fn add_metrics(self, metrics: {str: Metric})

    # Execution
    fn run(self, data: Iterable, max_epochs: Int = 1)
    fn terminate(self)  # Stop execution

    # State
    fn load_state_dict(self, state_dict: {str: any})
    fn state_dict(self) -> {str: any}
```

### Events

```simple
enum Events:
    STARTED
    EPOCH_STARTED
    ITERATION_STARTED
    ITERATION_COMPLETED
    EPOCH_COMPLETED
    COMPLETED
    EXCEPTION_RAISED

    # Periodic events
    fn ITERATION_COMPLETED(every: Int = null, once: Int = null) -> Event
    fn EPOCH_COMPLETED(every: Int = null, once: Int = null) -> Event
```

### State

```simple
class State:
    epoch: Int                  # Current epoch
    iteration: Int              # Global iteration
    epoch_iteration: Int        # Iteration within epoch
    max_epochs: Int             # Total epochs
    output: any                 # Process function output
    metrics: {str: F64}         # Computed metrics
    dataloader: Iterable        # Current dataloader
    batch: any                  # Current batch
    times: {str: F64}           # Timing information
```

---

## Testing Strategy

```simple
# test/unit/engine/engine_spec.spl
feature "Training Engine":
    scenario "Basic training loop":
        counter = {"count": 0}

        fn process(engine, batch):
            counter["count"] += 1
            return batch

        engine = Engine(process)
        data = [1, 2, 3, 4, 5]

        engine.run(data, max_epochs=2)

        assert counter["count"] == 10  # 5 batches × 2 epochs

    scenario "Event handlers":
        events_fired = []

        fn process(engine, batch):
            return batch

        engine = Engine(process)

        @engine.on(Events.STARTED)
        fn on_start(e):
            events_fired.append("started")

        @engine.on(Events.ITERATION_COMPLETED)
        fn on_iter(e):
            events_fired.append("iter")

        @engine.on(Events.EPOCH_COMPLETED)
        fn on_epoch(e):
            events_fired.append("epoch")

        engine.run([1, 2, 3], max_epochs=1)

        assert events_fired == ["started", "iter", "iter", "iter", "epoch"]

    scenario "Metrics computation":
        fn process(engine, batch):
            return {"pred": batch * 2, "label": batch * 2}

        engine = Engine(process)

        metric = Accuracy()
        engine.add_metric(metric, "acc")

        engine.run([1, 2, 3], max_epochs=1)

        assert engine.state.metrics["acc"] == 1.0  # Perfect accuracy
```

---

## Implementation Roadmap

### Phase 1: Core (v0.1)
- [ ] Engine class with state management
- [ ] Built-in events (STARTED, EPOCH_COMPLETED, etc.)
- [ ] Event handler attachment
- [ ] Basic training loop

### Phase 2: Metrics (v0.2)
- [ ] Metric base class
- [ ] Classification metrics (Accuracy, Precision, Recall, F1)
- [ ] Regression metrics (MSE, MAE, R2)
- [ ] Metric attachment to engine

### Phase 3: Handlers (v0.3)
- [ ] Checkpoint handler
- [ ] Early stopping
- [ ] LR scheduler integration
- [ ] Timer
- [ ] Progress bar
- [ ] Tracking integration

### Phase 4: Advanced (v0.4)
- [ ] Custom events
- [ ] Periodic events (every=N, once=N)
- [ ] Engine composition
- [ ] State serialization
- [ ] Distributed metrics

---

## References

- PyTorch Ignite: https://pytorch-ignite.ai/
- Catalyst: https://catalyst-team.github.io/catalyst/
- Lightning: https://lightning.ai/
- Feature tracking: `doc/feature/feature_db.sdn`
