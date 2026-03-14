# I/O & File System

This chapter covers file operations, path handling, and standard I/O in Simple.

## Standard I/O

### Output

```simple
print "Hello, world!"              # Print with newline
print "Value: {x}"                 # String interpolation
```

### Input

```simple
val line = read_line()              # Read a line from stdin
```

## File Operations

### Reading Files

```simple
use std.fs

val content = file_read("config.sdn")      # Read entire file as text
val lines = file_read_lines("data.txt")     # Read as list of lines
val bytes = file_read_bytes("image.png")    # Read as bytes
```

### Writing Files

```simple
use std.fs

file_write("output.txt", content)           # Write text to file
file_append("log.txt", "new entry\n")       # Append to file
file_write_bytes("output.bin", bytes)       # Write bytes
```

### File Existence and Metadata

```simple
use std.fs

file_exists("config.sdn")          # true/false
is_directory("src/")               # true/false
file_size("data.bin")              # Size in bytes
```

## Path Operations

```simple
use std.path

val p = join("src", "lib", "mod.spl")    # "src/lib/mod.spl"
val dir = dirname("src/lib/mod.spl")     # "src/lib"
val name = basename("src/lib/mod.spl")   # "mod.spl"
val ext = extension("mod.spl")           # "spl"
```

## Directory Operations

```simple
use std.fs

list_dir("src/")                    # List directory entries
create_dir("output/")               # Create directory
create_dir_all("a/b/c/")            # Create nested directories
```

## Environment

```simple
use std.fs

val home = env_get("HOME")
val cwd = cwd()
```

## SFFI Pattern

All I/O functions are wrappers around `extern fn rt_*` runtime functions:

```simple
extern fn rt_file_read_text(path: text) -> text

fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

See the [SFFI Guide](../ffi/sffi.md) for the full FFI pattern.

## See Also

- [Standard Library Overview](stdlib.md) for other stdlib modules
- [Module System](../language/module_system.md) for import patterns
- [Error Handling](../language/error_handling.md) for handling I/O errors with `Result`
