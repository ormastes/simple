# Configuration System (OmegaConf-like)

**Status:** Planned
**Target:** Simple 0.x
**Dependencies:** SDN parser, argparser stdlib
**Tracking:** Feature DB #TBD

---

## Overview

A hierarchical configuration system for Simple applications, inspired by OmegaConf but using SDN (Simple Data Notation) as the primary format. Provides type-safe, composable configurations with CLI overrides, interpolation, and validation.

### Design Goals

1. **SDN-first** - Native SDN format with human-readable syntax
2. **Composable** - Merge multiple config sources (files, CLI, env)
3. **Type-safe** - Runtime validation with schema enforcement
4. **Interpolation** - Variable references and custom resolvers
5. **Fail-fast** - Optional strict mode for missing values
6. **Frozen configs** - Immutable mode for production safety
7. **CLI integration** - Dotlist overrides (`train.epochs=10`)

---

## Core Features

### 1. Hierarchical Configuration

SDN's native structure maps directly to nested configs:

```sdn
# config/base.sdn
project = mnist
seed = 42

train:
    epochs = 10
    batch_size = 64
    lr = 1e-3
    out_dir = runs/${project}

model:
    type = resnet
    layers = [32, 64, 128]
    dropout = 0.1

dataset:
    root = ./data
    train_split = 0.8
    val_split = 0.1
    test_split = 0.1
```

### 2. Multiple Source Merging

```simple
# Load and merge configurations
base = Conf.load_sdn("config/base.sdn")
overrides = Conf.load_sdn("config/overrides.sdn")
cli_args = Conf.from_cli_dotlist(args)

# Later sources override earlier ones
cfg = Conf.merge(base, overrides, cli_args)
```

**Merge Strategy:**
- Scalars: later value replaces earlier
- Dicts: recursive merge (deep merge)
- Arrays: later array replaces earlier (no concatenation by default)
- Option: `Conf.merge_mode(append_arrays=true)` for array concatenation

### 3. CLI Dotlist Overrides

Command line syntax:
```bash
simple train config/base.sdn train.epochs=20 train.lr=5e-4 model.dropout=0.2
```

Library API:
```simple
# Parse from sys.args
args = sys.args[2..]  # Skip program name and script
overrides = Conf.from_cli_dotlist(args)

# Explicit parsing
overrides = Conf.parse_dotlist([
    "train.epochs=20",
    "train.lr=5e-4",
    "model.dropout=0.2"
])
```

**Type Coercion:**
- Numbers: `42`, `3.14`, `1e-3`
- Bools: `true`, `false`
- Strings: `"quoted"` or `unquoted`
- Arrays: `[1,2,3]`
- Dicts: `{key:val}`

### 4. Interpolation & Resolvers

**Variable References:**
```sdn
project = mnist
run_name = ${project}_exp1
out_dir = runs/${run_name}
checkpoint = ${out_dir}/best.pt
```

**Built-in Resolvers:**
```sdn
# Path operations
data_dir = ${path.join:${root},data,processed}
config_file = ${path.abspath:./config.sdn}

# Environment variables
home = ${env:HOME}
cuda_visible = ${env:CUDA_VISIBLE_DEVICES,0}  # with default

# Time/date
timestamp = ${time.now:%Y%m%d_%H%M%S}
date = ${time.now:%Y-%m-%d}

# System info
num_workers = ${sys.cpu_count}
hostname = ${sys.hostname}
```

**Custom Resolvers:**
```simple
# Register custom resolver
Conf.register_resolver("model_size") fn (arch: Str, scale: F64 = 1.0) -> Int:
    base_sizes = {"resnet": 50, "vgg": 16, "efficientnet": 8}
    return (base_sizes[arch] * scale).to_int()

# Use in config
# config.sdn
model:
    arch = resnet
    layers = ${model_size:${model.arch},1.5}  # Result: 75
```

**Resolution:**
```simple
cfg = Conf.load_sdn("config.sdn")
cfg = Conf.resolve(cfg)  # Resolve all interpolations

# Lazy resolution (resolve on access)
cfg = Conf.load_sdn("config.sdn", lazy_resolve=true)
val = cfg.train.epochs  # Resolves just this value
```

### 5. Structured Configs (Schema Validation)

**Schema Definition:**
```simple
# Define typed schema
schema TrainCfg:
    epochs: Int
    batch_size: Int
    lr: F64
    optimizer: Str
    checkpoint_every: Int = 1000  # with default

schema ModelCfg:
    type: Str
    layers: [Int]
    dropout: F64

    @validate
    fn check_dropout(self):
        assert self.dropout >= 0.0 and self.dropout <= 1.0, "dropout must be in [0, 1]"

schema AppCfg:
    project: Str
    seed: Int
    train: TrainCfg
    model: ModelCfg
```

**Validation:**
```simple
# Load untyped config
raw_cfg = Conf.load_sdn("config.sdn")

# Validate and convert
cfg: AppCfg = Conf.validate(AppCfg, raw_cfg, convert=true)

# Validation options
cfg = Conf.validate(
    AppCfg,
    raw_cfg,
    convert=true,           # "100" -> 100
    strict=true,            # Fail on extra fields
    allow_missing=false     # Fail on missing required fields
)
```

**Type Coercion Examples:**
```simple
# String to number
"100" -> 100
"3.14" -> 3.14

# Number to string
42 -> "42"

# String to bool
"true" -> true
"1" -> true
"yes" -> true
```

### 6. Missing Values & Fail-Fast

**Optional Values:**
```sdn
# Use null for optional
dataset:
    root = ./data
    cache_dir = null  # Optional
```

**Fail-Fast Mode:**
```simple
cfg = Conf.load_sdn("config.sdn")

# Fail on any missing value access
Conf.set_throw_on_missing(cfg, true)

# This throws if train.epochs is missing
epochs = cfg.train.epochs  # Error: Missing value at 'train.epochs'

# Check before access
if Conf.has_path(cfg, "train.epochs"):
    epochs = cfg.train.epochs
```

### 7. Frozen Configs

**Immutable Configuration:**
```simple
cfg = Conf.load_sdn("config.sdn")
cfg = Conf.freeze(cfg)

# This throws
cfg.train.epochs = 20  # Error: Cannot modify frozen config

# Check frozen state
if Conf.is_frozen(cfg):
    print("Config is immutable")

# Clone for modification
mutable_cfg = Conf.unfreeze(cfg)
mutable_cfg.train.epochs = 20  # OK
```

---

## API Reference

### Core Functions

```simple
# Loading
Conf.load_sdn(path: Str) -> Config
Conf.load_yaml(path: Str) -> Config  # YAML compatibility
Conf.from_dict(dict: {str: any}) -> Config
Conf.from_cli_dotlist(args: [Str]) -> Config

# Merging
Conf.merge(configs: ...Config) -> Config
Conf.merge_with(base: Config, overlay: Config, strategy: MergeStrategy) -> Config

# Access
cfg.path.to.value               # Dot notation
cfg["path"]["to"]["value"]       # Bracket notation
Conf.get(cfg, "path.to.value", default=null) -> any
Conf.has_path(cfg, "path.to.value") -> Bool

# Modification
Conf.set(cfg, "path.to.value", new_val)
Conf.delete(cfg, "path.to.value")
Conf.update(cfg, updates: {str: any})

# Interpolation
Conf.resolve(cfg) -> Config
Conf.register_resolver(name: Str, fn: Fn) -> None

# Validation
Conf.validate(schema: Type, cfg: Config, **opts) -> schema
Conf.set_throw_on_missing(cfg, enable: Bool)
Conf.check_schema(cfg, schema: Type) -> [ValidationError]

# State
Conf.freeze(cfg) -> Config
Conf.unfreeze(cfg) -> Config
Conf.is_frozen(cfg) -> Bool

# Serialization
Conf.to_sdn(cfg) -> Str
Conf.to_dict(cfg) -> {str: any}
Conf.save(cfg, path: Str)
```

### Built-in Resolvers

```simple
# Path operations
${path.join:part1,part2,...}
${path.abspath:rel_path}
${path.dirname:path}
${path.basename:path}
${path.exists:path}

# Environment
${env:VAR_NAME}
${env:VAR_NAME,default}

# Time
${time.now:format}        # strftime format
${time.unix}              # Unix timestamp

# System
${sys.cpu_count}
${sys.hostname}
${sys.platform}
${sys.cwd}
```

---

## Usage Examples

### Example 1: Training Script

```simple
import Conf from config
import Track from ml.tracking
import torch from ml.torch

# Load and merge configs
base = Conf.load_sdn("config/base.sdn")
cli = Conf.from_cli_dotlist(sys.args[1..])
cfg = Conf.merge(base, cli)
cfg = Conf.resolve(cfg)

# Validate schema
schema TrainConfig:
    project: Str
    train: {epochs: Int, lr: F64, batch_size: Int}
    model: {type: Str, layers: [Int]}

typed_cfg = Conf.validate(TrainConfig, cfg)

# Freeze for safety
cfg = Conf.freeze(cfg)

# Use in training
with Track.run(project=cfg.project, config=Conf.to_dict(cfg)) as run:
    model = create_model(cfg.model)

    for epoch in 0..cfg.train.epochs:
        loss = train_epoch(model, cfg)
        run.log({"loss": loss}, step=epoch)
```

### Example 2: Multi-Environment Configs

```sdn
# config/base.sdn
project = myapp
debug = false

database:
    host = localhost
    port = 5432
    pool_size = 10

# config/dev.sdn
debug = true
database:
    host = dev.db.local
    pool_size = 5

# config/prod.sdn
database:
    host = ${env:DB_HOST}
    port = ${env:DB_PORT,5432}
    pool_size = 50
```

```simple
# main.spl
env = sys.getenv("ENV", "dev")
base = Conf.load_sdn("config/base.sdn")
env_cfg = Conf.load_sdn(f"config/{env}.sdn")

cfg = Conf.merge(base, env_cfg)
cfg = Conf.resolve(cfg)

db_pool = connect_db(
    host=cfg.database.host,
    port=cfg.database.port,
    pool_size=cfg.database.pool_size
)
```

### Example 3: Hyperparameter Sweep

```simple
# Base config
base = Conf.load_sdn("config/base.sdn")

# Grid search
for lr in [1e-4, 1e-3, 1e-2]:
    for batch_size in [32, 64, 128]:
        # Create sweep config
        sweep_cfg = Conf.merge(base, Conf.from_dict({
            "train": {"lr": lr, "batch_size": batch_size},
            "run_name": f"lr{lr}_bs{batch_size}"
        }))

        run_training(sweep_cfg)
```

---

## Implementation Notes

### Phase 1: Core (v0.1)
- [x] SDN loading and parsing (already exists)
- [ ] `Conf.merge()` with deep merge
- [ ] Dot notation access
- [ ] CLI dotlist parsing
- [ ] Basic interpolation (`${var}`)

### Phase 2: Advanced (v0.2)
- [ ] Custom resolvers
- [ ] Built-in resolvers (path, env, time, sys)
- [ ] Schema validation with type coercion
- [ ] Freeze/unfreeze

### Phase 3: Production (v0.3)
- [ ] Lazy resolution
- [ ] Validation decorators
- [ ] Error messages with source location
- [ ] YAML compatibility layer
- [ ] Config diff tool

---

## Integration with Existing Simple Infrastructure

### SDN Parser Integration

The existing `src/sdn/` crate provides:
- `SdnDocument` for config loading
- `SdnValue` for hierarchical data
- Path queries via `get_path()`
- Ordered maps for deterministic iteration

**Mapping:**
```simple
# Conf wraps SdnDocument
class Config:
    _doc: SdnDocument
    _frozen: Bool
    _throw_on_missing: Bool

    fn get(self, path: Str, default: any = null) -> any:
        if self._throw_on_missing and not self._doc.has_path(path):
            throw MissingValueError(path)
        return self._doc.get_path(path) ?? default
```

### Argparser Integration

Use `simple/std_lib/src/cli/argparser.spl` (to be enhanced):
```simple
# Enhanced argparser for dotlist
class DotlistParser:
    fn parse(self, args: [Str]) -> {str: any}:
        result = {}
        for arg in args:
            if "=" in arg:
                path, value = arg.split("=", 1)
                self._set_nested(result, path.split("."), self._parse_value(value))
        return result
```

---

## Testing Strategy

### Unit Tests

```simple
# test/unit/config/conf_spec.spl
feature "Configuration System":
    scenario "Load SDN config":
        cfg = Conf.load_sdn("test/fixtures/simple.sdn")
        assert cfg.project == "test"
        assert cfg.train.epochs == 10

    scenario "Merge configs":
        base = Conf.from_dict({"a": 1, "b": {"c": 2}})
        over = Conf.from_dict({"b": {"d": 3}})
        merged = Conf.merge(base, over)
        assert merged.b.c == 2
        assert merged.b.d == 3

    scenario "CLI dotlist override":
        cli = Conf.parse_dotlist(["train.epochs=20", "train.lr=1e-3"])
        assert cli.train.epochs == 20
        assert cli.train.lr == 0.001

    scenario "Interpolation":
        cfg = Conf.from_dict({
            "base": "/data",
            "path": "${base}/train"
        })
        cfg = Conf.resolve(cfg)
        assert cfg.path == "/data/train"

    scenario "Schema validation":
        schema S:
            x: Int
            y: F64

        cfg = Conf.from_dict({"x": "42", "y": 3.14})
        typed = Conf.validate(S, cfg, convert=true)
        assert typed.x == 42
        assert typeof(typed.x) == Int
```

---

## Future Enhancements

1. **Config versioning** - Track schema changes
2. **Type inference** - Auto-generate schemas from usage
3. **Config documentation** - Extract docstrings from schemas
4. **Distributed configs** - Fetch from remote sources
5. **Config hot-reload** - Watch files for changes
6. **Encrypted values** - Secure sensitive data
7. **Config templates** - Jinja2-style templating

---

## References

- OmegaConf: https://omegaconf.readthedocs.io/
- Hydra: https://hydra.cc/
- SDN Format: `src/sdn/README.md`
- Feature tracking: `doc/feature/feature_db.sdn`
