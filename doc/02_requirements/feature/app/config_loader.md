# Config Loader Specification
*Source:* `test/feature/app/config_loader_spec.spl`

## Overview




## Overview

The config loader provides a Simple-native configuration format using `.spl`
syntax with variable assignments. It supports hierarchical config loading
with directory-based precedence.

## Config File Format

```simple
port = 8080
timeout = 30.5

logging = true
debug = false

name = "MyApp"

mode = PRODUCTION

ports = [8080, 8081, 8082]

train.epochs = 100
train.lr = 0.001
```

## Hierarchy & Precedence

Config files are searched from the current directory up to the project root.
Configs closer to the current directory override those higher in the hierarchy.

```
/project/__init__.spl          (lowest precedence)
/project/subdir/__init__.spl   (highest precedence)
```

## Behavior

it "gets simple values":
        val cfg = {"port": 8080, "logging": true}
        expect cfg["port"] == 8080
        expect cfg["logging"] == true

    it "gets nested values":
        val cfg = {"server": {"port": 8080}}
        expect cfg["server"]["port"] == 8080

    it "handles missing keys with default":
        val cfg = {"port": 8080}
        val missing = cfg["missing"] ?? nil
        expect missing == nil


# ============================================================================
# Config Merging
# ============================================================================

describe "Config Merging":

- parses basic integers
- parses floats
- parses booleans
- parses strings
- parses identifiers as constants
- parses arrays
- parses nested values with dotted keys
- skips comments
- skips empty lines
- handles multiline config


