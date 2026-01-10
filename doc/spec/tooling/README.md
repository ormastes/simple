# ML Tooling Specifications

This directory contains comprehensive specifications for the Simple ML tooling infrastructure, inspired by best-in-class Python ML tools but designed specifically for the Simple language ecosystem.

## Overview

The tooling suite provides three integrated systems that work together to create a complete ML development experience:

1. **Configuration System** (OmegaConf-like)
2. **Experiment Tracking** (W&B-like)
3. **Training Engine** (PyTorch Ignite-like)

## Documents

### [config_system.md](config_system.md)
**Configuration Management**

Hierarchical configuration system using SDN format as the primary source. Features:
- SDN-native format (human-readable, token-efficient)
- Multi-source merging (files + CLI + env)
- CLI dotlist overrides (`train.epochs=10`)
- Interpolation with custom resolvers (`${path.join:a,b}`)
- Type-safe schema validation with conversion
- Frozen configs for production safety

**Status:** Planned
**Dependencies:** SDN parser, argparser stdlib

### [experiment_tracking.md](experiment_tracking.md)
**Experiment Tracking & Management**

Local-first tracking system with optional remote sync. Features:
- Run lifecycle management with context managers
- Scalar, histogram, image, video, audio logging
- Offline mode (full functionality without network)
- Artifact versioning with lineage tracking
- Registry system for governance
- Hyperparameter sweeps (Bayesian/grid/random)
- Rich tables with typed columns
- Model watching (gradient/parameter tracking)

**Status:** Planned
**Dependencies:** Config system, file I/O, async operations

### [training_engine.md](training_engine.md)
**Event-Driven Training Engine**

Flexible, composable training loops with extensible handlers. Features:
- Generic `Engine` for any training/evaluation process
- Event system (STARTED, EPOCH_COMPLETED, etc.)
- Periodic events (`every=N`, `once=N`)
- Custom events for fine-grained control
- Built-in metrics (Accuracy, Precision, F1, etc.)
- Reusable handlers (Checkpoint, EarlyStopping, LRScheduler)
- Distributed training support
- Engine composition for complex workflows

**Status:** Planned
**Dependencies:** torch module, tracking system

## Integration

All three systems are designed to work together seamlessly:

```simple
# config_system.md - Load hierarchical config
cfg = Conf.load_sdn("config.sdn")
cli = Conf.from_cli_dotlist(sys.args)
cfg = Conf.merge(cfg, cli)

# experiment_tracking.md - Track experiments
with Track.run(project="cifar10", config=Conf.to_dict(cfg)) as run:
    # training_engine.md - Run training
    trainer = Engine(train_step)

    @trainer.on(Events.EPOCH_COMPLETED)
    fn log_metrics(engine):
        run.log({"loss": engine.state.metrics["loss"]}, step=engine.state.epoch)

    trainer.run(dataloader, max_epochs=cfg.train.epochs)
```

## Design Philosophy

### 1. Simple-Native
- Use SDN format instead of YAML/JSON where possible
- Leverage existing Simple infrastructure (mmap, async I/O, concurrent structures)
- Follow Simple language idioms and patterns

### 2. Local-First
- All operations work offline by default
- Data stored locally in `.simple/` directory
- Optional remote sync (doesn't break if unavailable)

### 3. Composable
- Each system works independently
- Clean APIs for integration
- No tight coupling between components

### 4. Minimal Boilerplate
- Context managers for resource management
- Sensible defaults everywhere
- Common patterns pre-built (checkpointing, early stopping, etc.)

### 5. Production-Ready
- Type-safe where possible (schema validation)
- Error handling with clear messages
- Performance-conscious (mmap, async I/O, concurrent structures)

## Relationship to Existing Infrastructure

These specs leverage existing Simple infrastructure:

**File I/O** (`src/runtime/src/value/file_io/`)
- Mmap for zero-copy data access
- Async file loading for background operations
- Platform-specific optimizations (fadvise, sendfile)

**SDN Parser** (`src/sdn/`)
- Native config format
- Ordered maps for deterministic iteration
- Path-based queries

**Concurrent Structures** (`src/runtime/src/concurrent/`)
- Lock-free maps for registries
- Thread-safe queues for async operations
- GC-aware write barriers

**Torch Module** (`simple/std_lib/src/ml/torch/`)
- Tensor operations
- Neural network layers
- Data loading infrastructure

## Implementation Status

All three specs are currently in **planning phase**. See individual documents for detailed roadmaps.

## Related Documents

- **Research:** `doc/research/torch_improvements.md` - Comprehensive research on mmap caching, runtime validation, and integration strategies
- **Feature Database:** `doc/feature/feature_db.sdn` - Feature tracking table
- **Guides:** `doc/guide/` - User guides and tutorials (TBD)

## Contributing

When implementing these specs:

1. Follow Simple coding standards (see `/coding` skill)
2. Use SSpec for tests (see `/sspec` skill)
3. Document thoroughly (inline + user guides)
4. Harmonize with existing infrastructure
5. Don't over-engineer - implement what's needed

## Questions?

For design questions or implementation guidance:
- Read the individual spec documents
- Check `doc/research/torch_improvements.md` for implementation details
- Reference existing Simple infrastructure patterns
- Consult with team if unclear

---

**Last Updated:** 2026-01-10
**Maintainer:** Simple ML Team
