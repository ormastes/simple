*Source: `simple/test/system/features/config/config_loader_spec.spl`*
*Last Updated: 2026-01-16*

---

# Config Loader Specification

**Feature ID:** TBD
**Category:** Configuration / File Loading
**Status:** Implemented

## Overview

The config loader provides a Simple-native configuration format using `.spl`
syntax with variable assignments. It supports hierarchical config loading
with directory-based precedence.

## Config File Format

```simple
# Numbers
port = 8080
timeout = 30.5

# Booleans
logging = true
debug = false

# Strings
name = "MyApp"

# Identifiers (constants)
mode = PRODUCTION

# Arrays
ports = [8080, 8081, 8082]

# Nested values (dotted keys)
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

Parse Simple-syntax config files into Config objects.

match config.parse_config_file(content):
            case Ok(dict):
                expect(dict["port"]).to(eq(8080))
                expect(dict["timeout"]).to(eq(30.5))
                expect(dict["logging"]).to(eq(true))
                expect(dict["app_name"]).to(eq("MyApp"))
                expect(dict["mode"]).to(eq("PRODUCTION"))
            case Err(_):
                fail("Parse failed")


# ============================================================================
# File Loading
# ============================================================================

describe "Config File Loading":

it "loads basic config from file":
        val fixture_path = "simple/test/fixtures/config/basic_config.spl"
        match config.from_file(fixture_path):
            case Ok(cfg):
                match cfg.get("port"):
                    case Some(p): expect(p).to(eq(8080))
                    case None: fail("Port not found")
                match cfg.get("logging"):
                    case Some(l): expect(l).to(eq(true))
                    case None: fail("Logging not found")
            case Err(msg):
                fail("Load failed: " + msg)

    it "loads nested config from file":
        val fixture_path = "simple/test/fixtures/config/nested_config.spl"
        match config.from_file(fixture_path):
            case Ok(cfg):
                match cfg.get("server.port"):
                    case Some(p): expect(p).to(eq(8080))
                    case None: fail("server.port not found")
                match cfg.get("train.epochs"):
                    case Some(e): expect(e).to(eq(100))
                    case None: fail("train.epochs not found")
            case Err(msg):
                fail("Load failed: " + msg)

    it "returns error for non-existent file":
        match config.from_file("nonexistent.spl"):
            case Ok(_):
                fail("Should have failed")
            case Err(msg):
                # Success - expected error
                pass


# ============================================================================
# Hierarchical Loading
# ============================================================================

describe "Hierarchical Config Loading":

it "loads from single config file":
        val root_path = "simple/test/fixtures/config/hierarchy/project_root.spl"
        match config.from_hierarchy(root_path):
            case Ok(cfg):
                match cfg.get("port"):
                    case Some(p): expect(p).to(eq(8080))
                    case None: fail("Port not found")
                match cfg.get("project_name"):
                    case Some(n): expect(n).to(eq("MyProject"))
                    case None: fail("Project name not found")
            case Err(msg):
                fail("Load failed: " + msg)

    it "returns empty config when no files found":
        match config.from_hierarchy("/nonexistent/path"):
            case Ok(cfg):
                match cfg.get("anything"):
                    case Some(_): fail("Should be empty")
                    case None: pass  # Expected
            case Err(msg):
                fail("Should return empty config, not error: " + msg)


# ============================================================================
# Config Access
# ============================================================================

describe "Config Access":

it "gets simple values":
        val cfg = config.from_dict({"port": 8080, "logging": true})
        match cfg.get("port"):
            case Some(p): expect(p).to(eq(8080))
            case None: fail("Port not found")

    it "gets nested values with dotted path":
        val cfg = config.from_dict({"server": {"port": 8080}})
        match cfg.get("server.port"):
            case Some(p): expect(p).to(eq(8080))
            case None: fail("Nested value not found")

    it "returns None for missing keys":
        val cfg = config.from_dict({"port": 8080})
        match cfg.get("missing"):
            case Some(_): fail("Should be None")
            case None: pass  # Expected


# ============================================================================
# Config Merging
# ============================================================================

describe "Config Merging":
