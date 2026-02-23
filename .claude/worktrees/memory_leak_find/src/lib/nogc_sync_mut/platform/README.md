# Platform Abstraction Library

**Location:** `src/lib/nogc_sync_mut/platform/`
**Status:** ✅ Production Ready
**Tests:** 5/5 files passing (80 individual tests)

## Quick Start (From Tests)

The platform library modules can be imported directly in test files:

```simple
use std.platform.config.{host_config, make_config, network_config}
use std.platform.convert.{send_u32, recv_u32, send_text, recv_text}
use std.platform.wire.{wire_writer_network, wire_reader_new}
use std.platform.text_io.{text_file_write_local, text_file_read_local}
```

## Modules

| Module | Purpose | Exports |
|--------|---------|---------|
| `config.spl` | Platform configuration | `PlatformConfig`, `host_config()`, `make_config()`, `network_config()`, `needs_swap()`, `same_platform()` |
| `convert.spl` | Value conversion | `send_u16/32/64()`, `recv_u16/32/64()`, `send_text()`, `recv_text()`, `send_bytes_u32()`, `recv_bytes_u32()` |
| `newline.spl` | Newline translation | `TextMode`, `translate_write()`, `translate_read()` |
| `wire.spl` | Wire format I/O | `WireWriter`, `WireReader`, constructors |
| `text_io.spl` | File I/O | `text_file_write()`, `text_file_read()`, local variants |
| `mod.spl` | Main module | Re-exports all of the above |

## Example Usage (From Tests)

See `test/unit/std/platform/*_spec.spl` for comprehensive examples:

### Configuration
```simple
use std.platform.config.{host_config, make_config, network_config}
use std.common.target.{TargetArch, TargetOS}

val host = host_config()                           # Auto-detect
val arm = make_config(TargetArch.Arm, TargetOS.Linux)  # Custom
val net = network_config()                         # Network byte order
```

### Endian Conversion
```simple
use std.platform.config.{host_config, network_config}
use std.platform.convert.{send_u32, recv_u32}

val host = host_config()
val net = network_config()
val wire_val = send_u32(host, net, 0x12345678)  # Big-endian
val local_val = recv_u32(host, net, wire_val)   # Back to host
```

### Text Conversion
```simple
use std.platform.config.{make_config}
use std.platform.convert.{send_text, recv_text}
use std.common.target.{TargetArch, TargetOS}

val unix = make_config(TargetArch.X86_64, TargetOS.Linux)
val win = make_config(TargetArch.X86_64, TargetOS.Windows)
val crlf = send_text(unix, win, "line1\nline2\n")  # → "line1\r\nline2\r\n"
```

### Wire Format
```simple
use std.platform.wire.{wire_writer_network, wire_reader_new}
use std.platform.config.{network_config}

# Write
var writer = wire_writer_network()
writer.write_u32(42)
writer.write_text("Hello")
val bytes = writer.to_bytes()

# Read
var reader = wire_reader_new(bytes, network_config())
val num = reader.read_u32()
val text = reader.read_text()
```

### File I/O
```simple
use std.platform.text_io.{text_file_write_local, text_file_read_local}

text_file_write_local("/tmp/test.txt", "line1\nline2\n")
val content = text_file_read_local("/tmp/test.txt")
```

## Testing

Run the comprehensive test suite:

```bash
bin/simple test test/unit/std/platform/
```

All tests verify:
- Same-platform operations are no-ops
- Cross-endian conversions preserve values
- Newline translation works correctly
- Wire format round-trips successfully
- File I/O handles platform differences

## Design

The library uses a **send/receive pattern**:

```
   Host                                    Remote
┌──────────┐                          ┌──────────┐
│ endian:LE│                          │ endian:BE│
│ nl: LF   │ ──send()─→ [convert] ──→ │ nl: CRLF │
│ ptr: 64  │                          │ ptr: 32  │
└──────────┘ ←─recv()─← [convert] ←── └──────────┘
```

**Key principle:** Convert at boundaries, not everywhere. When `host == remote`, conversions are no-ops (zero cost).

## Architecture

- **No generics** - Works in interpreter and compiled modes
- **Type-safe** - Must specify both platforms explicitly
- **Composable** - send/recv can be chained
- **Zero-cost** - Same-platform operations return unchanged values
- **Auto-detected** - `host_config()` detects everything

## See Also

- `README_PLATFORM_LIBRARY.md` - User guide
- `doc/report/platform_abstraction_implementation_2026-02-13.md` - Technical details
- `doc/report/platform_library_verification_2026-02-13.md` - Test verification
