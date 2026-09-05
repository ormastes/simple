# Userspace Path-Based Spawn API

Launch any executable by filesystem path with argument and environment vectors.

## Quick Start

```spl
use os.userlib.process.{spawn_path}

# Spawn /usr/bin/editor with arguments
val result = spawn_path("/usr/bin/editor", ["editor", "file.txt"], [])
if val Ok(pid) = result:
    print("Spawned process {pid}")
if val Err(errno) = result:
    print("Spawn failed: errno {errno}")
```

## API Reference

### `spawn_path(path: text, argv: [text], envp: [text]) -> Result<u32, i32>`

Spawn a new process from an executable at the given filesystem path.

| Parameter | Type | Description |
|-----------|------|-------------|
| `path` | `text` | Absolute path to the executable binary |
| `argv` | `[text]` | Argument vector; defaults to `[path]` when empty |
| `envp` | `[text]` | Environment variables as `KEY=VALUE` strings |

**Returns:** `Ok(pid)` on success, `Err(errno)` on failure.

### `sosix_marshal_string_vector(strings: [text]) -> [u8]`

Lower-level helper in `os.sosix.process`. Packs a text array into a
contiguous byte buffer with null-terminated strings followed by an offset
table (little-endian u64 entries) and a NULL terminator pointer.

### `sosix_marshal_string_vector_size(count: u64, total_string_bytes: u64) -> u64`

Compute the expected buffer size without allocating.

## Examples

### Shell usage

```spl
use os.userlib.process.{spawn_path, wait_}

val pid = spawn_path("/bin/ls", ["ls", "-la", "/home"], ["PATH=/bin"])
if val Ok(child) = pid:
    val status = wait_(child as u64)
```

### Programmatic spawn with environment

```spl
val envp: [text] = [
    "HOME=/home/user",
    "PATH=/bin:/usr/bin",
    "TERM=xterm-256color"
]
val result = spawn_path("/usr/bin/myapp", ["myapp", "--config", "/etc/app.conf"], envp)
```

### Empty argv defaults to path

```spl
# argv becomes ["/bin/hello"] automatically
val result = spawn_path("/bin/hello", [], [])
```

## Error Codes

| Errno | Constant | Meaning |
|-------|----------|---------|
| 2 | `ENOENT` | Executable not found at path |
| 8 | `ENOEXEC` | Invalid executable format |
| 12 | `ENOMEM` | Insufficient memory for process image |
| 22 | `EINVAL` | Empty path or invalid arguments |

## Kernel ABI Notes

The userspace `spawn_path()` invokes syscall 13 with:

| Arg | Purpose |
|-----|---------|
| arg0 | path pointer |
| arg1 | path length |
| arg2 | argv pointer (marshaled string vector) |
| arg3 | envp pointer (marshaled string vector) |

The current kernel handler reads arg0/arg1 (path) and treats arg2 as a
priority value. A future kernel ABI update will consume arg2/arg3 as
argv/envp pointers. Until then the marshaled buffers are prepared by
`spawn_path` but the kernel ignores them.
