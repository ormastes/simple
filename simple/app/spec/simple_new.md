# simple_new - Project Scaffolding

## Overview

Creates new Simple projects from templates with standard directory structure.

## Usage

```bash
simple_new myproject               # Create basic project
simple_new myproject --template lib    # Library project
simple_new myproject --template app    # Application project
simple_new myproject --template cli    # CLI application
simple_new myproject --template web    # Web application
```

## Options

| Flag | Description |
|------|-------------|
| `--template <name>` | Template: basic, lib, app, cli, web |
| `--no-git` | Don't initialize git/jj repository |
| `--no-spec` | Don't create spec test files |

## Templates

### basic (default)

Minimal project structure:

```
myproject/
├── simple.toml          # Project manifest
├── src/
│   ├── __init__.spl     # Module root
│   └── main.spl         # Entry point
└── test/
    └── main_spec.spl    # Basic test
```

### lib

Library project (no main):

```
myproject/
├── simple.toml
├── src/
│   ├── __init__.spl
│   └── lib.spl          # Library code
└── test/
    └── lib_spec.spl
```

### app

Application with structure:

```
myproject/
├── simple.toml
├── src/
│   ├── __init__.spl
│   ├── main.spl
│   ├── config.spl       # Configuration
│   └── utils.spl        # Utilities
└── test/
    ├── config_spec.spl
    └── utils_spec.spl
```

### cli

Command-line application:

```
myproject/
├── simple.toml
├── src/
│   ├── __init__.spl
│   ├── main.spl
│   ├── args.spl         # Argument parsing
│   └── commands/
│       ├── __init__.spl
│       └── run.spl
└── test/
    └── args_spec.spl
```

### web

Web application:

```
myproject/
├── simple.toml
├── src/
│   ├── __init__.spl
│   ├── main.spl
│   ├── routes.spl
│   ├── handlers/
│   │   └── __init__.spl
│   └── templates/
│       └── index.html
├── static/
│   ├── css/
│   └── js/
└── test/
    └── routes_spec.spl
```

## Generated Files

### simple.toml

```toml
[package]
name = "myproject"
version = "0.1.0"
edition = "2025"

[dependencies]
# Add dependencies here

[dev-dependencies]
# Add test dependencies here
```

### src/main.spl (app)

```simple
"""
MyProject - Brief description
"""

extern fn sys_get_args() -> List[String]

async fn main() -> Int:
    let args = sys_get_args()
    print("Hello from myproject!")
    return 0
```

### src/__init__.spl

```simple
"""
MyProject module
"""

pub use main.*
```

### test/main_spec.spl

```simple
"""
Tests for main module
"""

import spec.{describe, it, expect}

describe "main":
    it "should run successfully":
        expect(true).to_be(true)
```

## Implementation Notes

1. Parse command-line arguments
2. Validate project name (alphanumeric, underscores)
3. Check directory doesn't exist
4. Create directory structure
5. Write template files
6. Initialize jj repository (unless --no-git)
7. Print success message

## Dependencies

- `native_fs_write_string` - File writing
- `native_fs_exists` - File/directory existence
- `sys_get_args` - Command-line arguments

## Example

```bash
$ simple_new myapp --template cli

Creating project 'myapp' with template 'cli'...

Created:
  myapp/simple.toml
  myapp/src/__init__.spl
  myapp/src/main.spl
  myapp/src/args.spl
  myapp/src/commands/__init__.spl
  myapp/src/commands/run.spl
  myapp/test/args_spec.spl

Initialized jj repository.

Done! To get started:
  cd myapp
  simple src/main.spl
```
