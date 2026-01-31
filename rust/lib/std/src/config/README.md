# Simple Configuration System

Simple-native configuration management with hierarchical loading and precedence.

## Features

- **Simple-syntax config files**: Use familiar variable assignment syntax
- **Hierarchical loading**: Auto-discover and merge configs from directory tree
- **Type support**: Numbers, booleans, strings, identifiers, arrays
- **Nested values**: Use dotted keys for nested configuration
- **Flexible precedence**: Directory-level configs override parent configs

## Config File Format

Config files use Simple syntax with variable assignments:

```simple
# Numbers
port = 8080
timeout = 30.5

# Booleans
logging = true
debug = false

# Strings
app_name = "MyApp"
host = "localhost"

# Identifiers (constants)
mode = PRODUCTION
log_level = INFO

# Arrays
ports = [8080, 8081, 8082]
allowed_hosts = ["localhost", "127.0.0.1"]

# Nested values (dotted keys)
database.host = "db.example.com"
database.port = 5432
database.name = "myapp"

train.epochs = 100
train.batch_size = 32
train.lr = 0.001
```

## API

### Parsing

```simple
import config

# Parse config from string
val text = "port = 8080\nlogging = true"
match config.parse_config_file(text):
    case Ok(dict):
        println(dict["port"])  # 8080
    case Err(msg):
        println("Parse error: " + msg)
```

### Loading from File

```simple
# Load single config file
match config.from_file("config.spl"):
    case Ok(cfg):
        match cfg.get("port"):
            case Some(p): println("Port: " + str(p))
            case None: println("Not configured")
    case Err(msg):
        println("Error: " + msg)
```

### Hierarchical Loading

Automatically discovers and merges `__init__.spl` files from current directory up to project root:

```simple
# Given:
#   /project/__init__.spl:        port = 8080, logging = true
#   /project/subdir/__init__.spl: port = 9000, debug = true
#
# Load from /project/subdir:
match config.from_hierarchy("/project/subdir"):
    case Ok(cfg):
        cfg.get("port")   # Some(9000) - subdir overrides
        cfg.get("logging") # Some(true) - inherited from parent
        cfg.get("debug")   # Some(true) - from subdir
```

### Accessing Values

```simple
val cfg = config.from_dict({"port": 8080, "server": {"host": "localhost"}})

# Simple values
match cfg.get("port"):
    case Some(p): println(p)  # 8080
    case None: println("Not found")

# Nested values with dotted path
match cfg.get("server.host"):
    case Some(h): println(h)  # "localhost"
    case None: println("Not found")
```

### Merging Configs

```simple
val base = config.from_dict({"a": 1, "b": 2})
val overlay = config.from_dict({"b": 3, "c": 4})
val merged = config.merge(base, overlay)

merged.get("a")  # Some(1)
merged.get("b")  # Some(3) - overlay wins
merged.get("c")  # Some(4)
```

## Precedence Policy

When using `from_hierarchy()`, configs are merged with this precedence (lowest to highest):

1. **Project root** (`/project/__init__.spl`)
2. **Parent directories** (`/project/parent/__init__.spl`)
3. **Current directory** (`/project/parent/current/__init__.spl`)
4. **Environment variables** (future)
5. **CLI flags** (future)

Configs closer to the current directory override those higher in the hierarchy.

## Common Patterns

### Application Configuration

```simple
class AppConfig:
    port: i32
    host: str
    debug: bool

    static fn load(path: str) -> Result<AppConfig, str>:
        match config.from_file(path):
            case Ok(cfg):
                val port = cfg.get("port").unwrap_or(8080)
                val host = cfg.get("host").unwrap_or("localhost")
                val debug = cfg.get("debug").unwrap_or(false)
                return Ok(AppConfig(port, host, debug))
            case Err(msg):
                return Err(msg)
```

### Multi-Environment Config

```simple
fn load_env_config(env: str) -> Config:
    val base = config.from_file("config/base.spl").unwrap()
    val env_file = "config/" + env + ".spl"

    match config.from_file(env_file):
        case Ok(env_cfg):
            return config.merge(base, env_cfg)
        case Err(_):
            return base
```

### Training Configuration

```simple
# train_config.spl
train.epochs = 100
train.batch_size = 32
train.lr = 0.001
train.optimizer = ADAM

model.hidden_size = 256
model.num_layers = 4
model.dropout = 0.1

# Load it:
match config.from_file("train_config.spl"):
    case Ok(cfg):
        val epochs = cfg.get("train.epochs")
        val lr = cfg.get("train.lr")
        val hidden = cfg.get("model.hidden_size")
```

## Examples

See `simple/std_lib/example/config_example.spl` for complete usage examples.

## Implementation Details

- **Parser**: Lightweight parser for Simple-syntax variable assignments
- **No dynamic imports**: Config files are parsed statically, not executed as modules
- **Type preservation**: Values retain their types (int, float, bool, string, array)
- **Error handling**: All operations return `Result` types for safe error handling

## Future Enhancements

- Environment variable substitution: `port = ${PORT:8080}`
- TOML/JSON format support (in addition to Simple syntax)
- Config validation against schemas
- Hot-reload support for config changes
- Encrypted config values
