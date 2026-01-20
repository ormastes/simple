# Semantic Types - Quick Reference Guide
**Simple Language Standard Library**
**Last Updated**: 2026-01-20

---

## Quick Lookup: When to Use Which Type

### I/O Operations

**Reading/Writing Data**:
```simple
// File I/O
use units.size::ByteCount
write_text(path, content)?            // Returns Result<ByteCount, IoError>
read_exact(1024_bytes)?               // Takes ByteCount parameter

// Network I/O
stream.read(&mut buffer, 1024_bytes)? // Returns Result<ByteCount, NetError>
stream.write(data)?                   // Returns Result<ByteCount, NetError>
socket.send_to(data, addr)?           // Returns Result<ByteCount, NetError>
socket.recv_from(&mut buf, 2048_bytes)? // Returns Result<(ByteCount, text), NetError>
```

**Files**:
```simple
use units.size::FileSize
use units.file::FilePath
```

---

### Time & Duration

**Short Durations (milliseconds)**:
```simple
use units.time::Milliseconds

// Session times
session.get_age()                     // Returns Milliseconds
session.is_idle(30000_ms)             // Takes Milliseconds

// File timestamps
metadata.last_modified                // Type: Milliseconds

// TUI timeouts
read_event(100_ms)                    // Takes Milliseconds
```

**Long Intervals (seconds)**:
```simple
use units.time::Seconds

// Network keepalive
stream.set_keepalive(Some(30_s))?     // Takes Option<Seconds>
```

**Nanoseconds**:
```simple
use units.time::Nanoseconds

// High-precision timing
```

---

### Counting & Indexing

**Generic Counts**:
```simple
use units.core::Count

workspace.file_count()                // Returns Count
workspace.dirty_count()               // Returns Count
staged_files.count()                  // Returns Count
```

**Array/Collection Indices**:
```simple
use units.core::Index

// For array indexing where -1 means invalid
```

**Capacities & Lengths**:
```simple
use units.core::Capacity
use units.core::Length
```

---

### Graphics

**PBR Materials (0.0-1.0 range)**:
```simple
use units.graphics::{Metallic, Roughness, AmbientOcclusion, Opacity, Reflectance}

material.metallic = 0.8_metallic      // Not mixable with roughness
material.roughness = 0.5_roughness    // Type-safe material properties
material.ambient_occlusion = 1.0_ao
```

**Light Intensity**:
```simple
use units.graphics::Intensity

light.intensity = 10.0_intensity
```

**Graphics Counts**:
```simple
use units.graphics::{PixelCount, VertexCount, TextureSize, IndexCount}
```

**Graphics Indices**:
```simple
use units.graphics::{VertexIndex, LightIndex, LayerIndex, MipLevel}
```

---

### UI Layout

**Pixel Dimensions**:
```simple
use units.ui::PixelDimension

EdgeInsets {
    top: 10_px_dim,
    right: 5_px_dim,
    bottom: 10_px_dim,
    left: 5_px_dim
}

BoxConstraints {
    min_width: Some(100_px_dim),
    max_width: Some(800_px_dim),
    min_height: Some(50_px_dim),
    max_height: None
}
```

---

### Network

**Ports**:
```simple
use units.net::Port

listener.bind("127.0.0.1", 8080_port)?
```

**Buffer Sizes**:
```simple
use units.net::{BufferSize, PacketSize}
```

**Connection Limits**:
```simple
use units.net::ConnectionLimit

server.set_max_connections(100_connlim)
```

**Network Shutdown**:
```simple
use units.net::ShutdownMode

stream.shutdown(ShutdownMode::Both)?
stream.shutdown(ShutdownMode::Read)?
stream.shutdown(ShutdownMode::Write)?
```

---

### LMS / Language Model Server

**Session Management**:
```simple
use units.lms::{StateId, SessionId, MessageId}

session.id                            // Type: SessionId
message.id                            // Type: MessageId
```

**Document Versioning (LSP)**:
```simple
use units.lms::DocumentVersion

FileMetadata.new(uri, 1_doc_ver, content)
metadata.version.increment()          // Returns DocumentVersion
```

**Token Counting**:
```simple
use units.lms::TokenCount

if total_tokens.exceeds(TokenCount::limit_claude()):
    truncate_context()

remaining = limit.remaining(used)     // Returns TokenCount
```

**LLM Parameters**:
```simple
use units.lms::{Temperature, Probability}

config.temperature = 0.7_temp         // Balanced creativity
config.top_p = 0.9_prob              // Nucleus sampling
```

---

### Identifiers

**Request/Entity IDs**:
```simple
use units.ids::{RequestId, EntityId}
```

**Hash Values**:
```simple
use units.core::{Hash, Checksum}
```

---

## Common Patterns

### Converting to/from Primitives

**From primitives**:
```simple
val count = Count::from_i64(42)
val bytes = ByteCount::from_i64(1024)
val time = Milliseconds::from_u64(5000)
```

**To primitives**:
```simple
val count_val = count.value()         // i64
val bytes_val = bytes.value()         // u64
val time_val = time.value()           // u64
```

**Literal syntax**:
```simple
val count = 42_count
val bytes = 1024_bytes
val time = 5000_ms
val temp = 0.7_temp
val metallic = 0.8_metallic
```

### Working with Option Types

```simple
// Option<Seconds> for enable/disable
stream.set_keepalive(Some(30_s))?     // Enable with 30 seconds
stream.set_keepalive(None)?           // Disable

// Option<PixelDimension> for constraints
BoxConstraints {
    min_width: Some(100_px_dim),      // Constrained
    max_width: None                   // Unconstrained
}
```

### Comparing and Arithmetic

**Comparisons**:
```simple
if session.get_age().exceeds(3600000_ms):
    cleanup_session()

if bytes_written.value() > 0:
    println("Wrote data")
```

**Arithmetic**:
```simple
val total = count1.add(count2)        // Returns Count
val remaining = limit.sub(used)       // Returns ByteCount
val incremented = version.increment() // Returns DocumentVersion
```

---

## Type Safety Examples

### ✅ Correct Usage

```simple
// Type-safe I/O
val n = stream.read(&mut buffer, 1024_bytes)?
println("Read {n.value()} bytes")

// Type-safe materials
material.set_properties(0.8_metallic, 0.5_roughness)

// Type-safe time
session.is_idle(30000_ms)

// Type-safe dimensions
EdgeInsets::all(10_px_dim)
```

### ❌ Compile Errors (Type Safety Working)

```simple
// Can't mix different types
stream.read(&mut buffer, packet_count)?  // Error! i32 != ByteCount

// Can't swap parameters
material.set_properties(roughness, metallic)  // Error! Type mismatch

// Can't mix time units
session.is_idle(30_s)                   // Error! Seconds != Milliseconds

// Can't use wrong dimension type
EdgeInsets::all(10)                     // Error! i32 != PixelDimension
```

---

## Helper Methods Reference

### Common Helpers (Available on Most Types)

```simple
// Construction
Type::from_i32(n)
Type::from_i64(n)
Type::from_u64(n)
Type::from_f32(n)

// Conversion
.value()                              // Get underlying value
.to_i32()                            // Convert to i32 (may saturate)

// Constants
Type::zero()                         // Zero value
Type::initial()                      // Initial/default value

// Checks
.is_zero()                          // Check if zero
.is_valid()                         // Check if valid (>= 0)

// Arithmetic
.add(other)                         // Add two values
.sub(other)                         // Subtract (may saturate)
.increment()                        // Add 1

// Comparisons
.exceeds(limit)                     // Check if > limit
.is_newer_than(other)               // For versions
.is_older_than(other)               // For versions
```

### Type-Specific Helpers

**Milliseconds**:
```simple
.to_duration()                      // Convert to Duration
.to_secs()                          // Convert to seconds (u64)
```

**Metallic**:
```simple
.is_metal()                         // Check if metallic (>= 0.9)
.is_dielectric()                    // Check if non-metallic (<= 0.1)
```

**PixelDimension**:
```simple
.clamp(min, max)                    // Clamp to range
.max_with(other)                    // Get maximum
.min_with(other)                    // Get minimum
.abs()                              // Absolute value
```

**TokenCount**:
```simple
.limit_gpt3()                       // 4096 tokens
.limit_gpt4()                       // 8192 tokens
.limit_claude()                     // 100k tokens
.percentage_of(total)               // Calculate percentage
.remaining(limit)                   // Calculate remaining
```

**Temperature**:
```simple
.deterministic()                    // 0.0
.balanced()                         // 0.7
.creative()                         // 1.0
.is_deterministic()                 // Check if < 0.01
.is_high()                          // Check if > 1.2
```

---

## Import Guide

### All Types Available Through

```simple
import units.*                       // Import all types

// Or import specific modules
import units.core::*                 // Count, Index, Hash, etc.
import units.time::*                 // Seconds, Milliseconds, Nanoseconds
import units.size::*                 // ByteCount, FileSize
import units.graphics::*             // Metallic, Roughness, etc.
import units.net::*                  // Port, ShutdownMode, etc.
import units.lms::*                  // SessionId, TokenCount, etc.
import units.ui::*                   // PixelDimension
import units.file::*                 // FilePath, FileSize
import units.ids::*                  // RequestId, EntityId
```

---

## Best Practices

### ✅ DO

- **Use semantic types** for public APIs
- **Use literal syntax** for clarity: `1024_bytes` not `ByteCount::from_i64(1024)`
- **Add helper methods** specific to your domain
- **Convert at FFI boundaries** (extern functions stay primitive)
- **Use type suffixes** for self-documenting code

### ❌ DON'T

- **Don't wrap math functions** (max, min, sqrt stay primitive)
- **Don't wrap boolean predicates** (is_empty() returns bool, not IsEmpty)
- **Don't wrap JSON types** (breaks spec compliance)
- **Don't create generic wrappers** (use domain-specific types instead)

---

## When to Create New Types

**Create a new type when**:
✅ The value represents a domain concept (e.g., `Altitude`)
✅ Confusion is likely (e.g., document version vs line number)
✅ Type safety prevents bugs (e.g., metallic vs roughness)

**Don't create a new type when**:
❌ It's a mathematical operation (max, min, sqrt)
❌ It's a universal predicate (is_empty, has_*)
❌ It's spec-mandated (JSON bool/f64/i64)
❌ It's inherently generic (generic parameters in templates)

---

## Performance Note

**Zero-Cost Abstractions**: All unit types compile to their underlying primitives with zero runtime overhead. Using semantic types has no performance penalty.

---

## Need Help?

**Documentation**:
- Design patterns: `doc/guide/newtype_design_patterns.md`
- Full project report: `doc/report/primitive_api_migration_summary_2026-01-20.md`
- Future opportunities: `doc/guide/primitive_api_next_steps.md`

**Questions?**:
- Check the comprehensive guides in `doc/guide/`
- Review session reports in `doc/report/`
- See examples in stdlib modules

---

**Quick Reference Version**: 1.0
**Last Updated**: 2026-01-20
**Project Status**: Production Ready ✅
