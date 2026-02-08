# Lyon 2D Graphics SFFI Implementation Guide

**Status**: SFFI wrapper complete, Rust runtime implementation needed
**Created**: 2026-02-08
**Files**:
- SFFI Wrapper: `src/app/io/graphics2d_ffi.spl` (~700 lines)
- Test Spec: `test/app/io/graphics2d_ffi_spec.spl` (~450 lines)
- Demo: `examples/graphics2d_demo.spl` (~180 lines)

## Overview

This guide explains how to implement the Rust runtime side of the Lyon 2D vector graphics tessellation SFFI wrapper for the Simple language compiler.

The Simple-side wrapper is **complete** and follows the two-tier SFFI pattern. This document covers the Rust implementation needed to make the wrapper functional.

## What is Lyon?

Lyon is a Rust library for GPU-based 2D vector graphics. It:
- **Tessellates** vector paths into triangles for GPU rendering
- Handles **fill** and **stroke** operations
- Provides **path builders** for complex shapes
- Supports **transforms**, **bezier curves**, and **shape primitives**

**Use cases**: Vector graphics, UI rendering, data visualization, games

## Architecture

### Two-Tier SFFI Pattern

**Tier 1: Extern Declarations** (Simple)
```simple
extern fn rt_lyon_path_circle(center_x: f64, center_y: f64, radius: f64) -> i64
extern fn rt_lyon_fill_tessellate(path: i64, tolerance: f64) -> i64
```

**Tier 2: Simple Wrappers** (Simple)
```simple
fn graphics_circle(center: Point2D, radius: f64) -> Path:
    val handle = rt_lyon_path_circle(center.x, center.y, radius)
    Path(handle: handle, is_valid: handle != 0)
```

**Runtime Implementation** (Rust - to be implemented)
```rust
#[no_mangle]
pub extern "C" fn rt_lyon_path_circle(center_x: f64, center_y: f64, radius: f64) -> i64 {
    // Implementation here
}
```

## Rust Dependencies

Add to runtime's `Cargo.toml`:

```toml
[dependencies]
lyon = "1.0"  # Or latest version
lyon_tessellation = "1.0"
lyon_path = "1.0"
lyon_geom = "1.0"
```

## Implementation Strategy

### 1. Handle Management

Lyon uses owned types, but we expose opaque `i64` handles to Simple:

```rust
use std::collections::HashMap;
use std::sync::Mutex;
use lyon::path::Path as LyonPath;
use lyon::path::builder::{PathBuilder as LyonPathBuilder, Build};
use lyon::tessellation::*;
use lyon::geom::{Point, Vector};

// Global state (thread-safe)
lazy_static! {
    static ref PATH_BUILDERS: Mutex<HashMap<i64, LyonPathBuilder>> = Mutex::new(HashMap::new());
    static ref PATHS: Mutex<HashMap<i64, LyonPath>> = Mutex::new(HashMap::new());
    static ref FILL_TESSELLATIONS: Mutex<HashMap<i64, FillTessOutput>> = Mutex::new(HashMap::new());
    static ref STROKE_TESSELLATIONS: Mutex<HashMap<i64, StrokeTessOutput>> = Mutex::new(HashMap::new());
    static ref VERTEX_BUFFERS: Mutex<HashMap<i64, Vec<Vertex>>> = Mutex::new(HashMap::new());
    static ref INDEX_BUFFERS: Mutex<HashMap<i64, Vec<u32>>> = Mutex::new(HashMap::new());
    static ref NEXT_PATH_BUILDER_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_PATH_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_TESS_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_BUFFER_ID: Mutex<i64> = Mutex::new(1);
}

#[derive(Clone)]
struct Vertex {
    position: Point<f32>,
    normal: Vector<f32>,
}

struct FillTessOutput {
    vertices: Vec<Vertex>,
    indices: Vec<u32>,
}

struct StrokeTessOutput {
    vertices: Vec<Vertex>,
    indices: Vec<u32>,
}
```

### 2. Path Builder Implementation

```rust
use lyon::path::builder::{PathBuilder, Build};
use lyon::path::Path;
use lyon::geom::Point;

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_new() -> i64 {
    let builder = Path::builder();

    let mut builders = PATH_BUILDERS.lock().unwrap();
    let mut next_id = NEXT_PATH_BUILDER_ID.lock().unwrap();

    let id = *next_id;
    *next_id += 1;

    builders.insert(id, builder);
    id
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_free(builder_id: i64) -> bool {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    builders.remove(&builder_id).is_some()
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_begin(builder_id: i64, x: f64, y: f64) -> bool {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    if let Some(builder) = builders.get_mut(&builder_id) {
        builder.begin(Point::new(x as f32, y as f32));
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_line_to(builder_id: i64, x: f64, y: f64) -> bool {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    if let Some(builder) = builders.get_mut(&builder_id) {
        builder.line_to(Point::new(x as f32, y as f32));
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_quadratic_bezier_to(
    builder_id: i64,
    ctrl_x: f64,
    ctrl_y: f64,
    to_x: f64,
    to_y: f64,
) -> bool {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    if let Some(builder) = builders.get_mut(&builder_id) {
        builder.quadratic_bezier_to(
            Point::new(ctrl_x as f32, ctrl_y as f32),
            Point::new(to_x as f32, to_y as f32),
        );
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_cubic_bezier_to(
    builder_id: i64,
    ctrl1_x: f64,
    ctrl1_y: f64,
    ctrl2_x: f64,
    ctrl2_y: f64,
    to_x: f64,
    to_y: f64,
) -> bool {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    if let Some(builder) = builders.get_mut(&builder_id) {
        builder.cubic_bezier_to(
            Point::new(ctrl1_x as f32, ctrl1_y as f32),
            Point::new(ctrl2_x as f32, ctrl2_y as f32),
            Point::new(to_x as f32, to_y as f32),
        );
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_close(builder_id: i64) -> bool {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    if let Some(builder) = builders.get_mut(&builder_id) {
        builder.close();
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_builder_build(builder_id: i64) -> i64 {
    let mut builders = PATH_BUILDERS.lock().unwrap();
    if let Some(builder) = builders.remove(&builder_id) {
        let path = builder.build();

        let mut paths = PATHS.lock().unwrap();
        let mut next_id = NEXT_PATH_ID.lock().unwrap();

        let id = *next_id;
        *next_id += 1;

        paths.insert(id, path);
        id
    } else {
        0
    }
}
```

### 3. Shape Primitives

```rust
use lyon::path::Path;
use lyon::path::builder::BorderRadii;
use lyon::geom::{Point, Size, Box2D};

#[no_mangle]
pub extern "C" fn rt_lyon_path_rectangle(
    x: f64,
    y: f64,
    width: f64,
    height: f64,
) -> i64 {
    let mut builder = Path::builder();
    let rect = Box2D::new(
        Point::new(x as f32, y as f32),
        Point::new((x + width) as f32, (y + height) as f32),
    );
    builder.add_rectangle(&rect, Winding::Positive);
    let path = builder.build();

    let mut paths = PATHS.lock().unwrap();
    let mut next_id = NEXT_PATH_ID.lock().unwrap();

    let id = *next_id;
    *next_id += 1;

    paths.insert(id, path);
    id
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_circle(
    center_x: f64,
    center_y: f64,
    radius: f64,
) -> i64 {
    let mut builder = Path::builder();
    builder.add_circle(
        Point::new(center_x as f32, center_y as f32),
        radius as f32,
        Winding::Positive,
    );
    let path = builder.build();

    let mut paths = PATHS.lock().unwrap();
    let mut next_id = NEXT_PATH_ID.lock().unwrap();

    let id = *next_id;
    *next_id += 1;

    paths.insert(id, path);
    id
}

#[no_mangle]
pub extern "C" fn rt_lyon_path_ellipse(
    center_x: f64,
    center_y: f64,
    radius_x: f64,
    radius_y: f64,
) -> i64 {
    let mut builder = Path::builder();
    builder.add_ellipse(
        Point::new(center_x as f32, center_y as f32),
        Vector::new(radius_x as f32, radius_y as f32),
        Angle::radians(0.0),
        Winding::Positive,
    );
    let path = builder.build();

    let mut paths = PATHS.lock().unwrap();
    let mut next_id = NEXT_PATH_ID.lock().unwrap();

    let id = *next_id;
    *next_id += 1;

    paths.insert(id, path);
    id
}
```

### 4. Fill Tessellation

```rust
use lyon::tessellation::*;

struct FillVertexCtor;

impl FillVertexConstructor<Vertex> for FillVertexCtor {
    fn new_vertex(&mut self, vertex: FillVertex) -> Vertex {
        Vertex {
            position: vertex.position(),
            normal: Vector::new(0.0, 0.0), // No normals for fill
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_fill_tessellate(path_id: i64, tolerance: f64) -> i64 {
    let paths = PATHS.lock().unwrap();
    if let Some(path) = paths.get(&path_id) {
        let mut geometry = VertexBuffers::new();
        let mut tessellator = FillTessellator::new();

        let options = FillOptions::tolerance(tolerance as f32);

        if tessellator.tessellate_path(
            path,
            &options,
            &mut BuffersBuilder::new(&mut geometry, FillVertexCtor),
        ).is_ok() {
            let output = FillTessOutput {
                vertices: geometry.vertices,
                indices: geometry.indices,
            };

            let mut tessellations = FILL_TESSELLATIONS.lock().unwrap();
            let mut next_id = NEXT_TESS_ID.lock().unwrap();

            let id = *next_id;
            *next_id += 1;

            tessellations.insert(id, output);
            return id;
        }
    }
    0
}

#[no_mangle]
pub extern "C" fn rt_lyon_fill_tessellation_vertex_count(tess_id: i64) -> i64 {
    let tessellations = FILL_TESSELLATIONS.lock().unwrap();
    if let Some(tess) = tessellations.get(&tess_id) {
        tess.vertices.len() as i64
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_fill_tessellation_index_count(tess_id: i64) -> i64 {
    let tessellations = FILL_TESSELLATIONS.lock().unwrap();
    if let Some(tess) = tessellations.get(&tess_id) {
        tess.indices.len() as i64
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_fill_tessellation_get_vertices(tess_id: i64) -> i64 {
    let tessellations = FILL_TESSELLATIONS.lock().unwrap();
    if let Some(tess) = tessellations.get(&tess_id) {
        let vertices = tess.vertices.clone();

        let mut buffers = VERTEX_BUFFERS.lock().unwrap();
        let mut next_id = NEXT_BUFFER_ID.lock().unwrap();

        let id = *next_id;
        *next_id += 1;

        buffers.insert(id, vertices);
        id
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_fill_tessellation_get_indices(tess_id: i64) -> i64 {
    let tessellations = FILL_TESSELLATIONS.lock().unwrap();
    if let Some(tess) = tessellations.get(&tess_id) {
        let indices = tess.indices.clone();

        let mut buffers = INDEX_BUFFERS.lock().unwrap();
        let mut next_id = NEXT_BUFFER_ID.lock().unwrap();

        let id = *next_id;
        *next_id += 1;

        buffers.insert(id, indices);
        id
    } else {
        0
    }
}
```

### 5. Stroke Tessellation

```rust
struct StrokeVertexCtor;

impl StrokeVertexConstructor<Vertex> for StrokeVertexCtor {
    fn new_vertex(&mut self, vertex: StrokeVertex) -> Vertex {
        Vertex {
            position: vertex.position(),
            normal: vertex.normal(),
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_stroke_tessellate(
    path_id: i64,
    width: f64,
    tolerance: f64,
) -> i64 {
    let paths = PATHS.lock().unwrap();
    if let Some(path) = paths.get(&path_id) {
        let mut geometry = VertexBuffers::new();
        let mut tessellator = StrokeTessellator::new();

        let options = StrokeOptions::tolerance(tolerance as f32)
            .with_line_width(width as f32);

        if tessellator.tessellate_path(
            path,
            &options,
            &mut BuffersBuilder::new(&mut geometry, StrokeVertexCtor),
        ).is_ok() {
            let output = StrokeTessOutput {
                vertices: geometry.vertices,
                indices: geometry.indices,
            };

            let mut tessellations = STROKE_TESSELLATIONS.lock().unwrap();
            let mut next_id = NEXT_TESS_ID.lock().unwrap();

            let id = *next_id;
            *next_id += 1;

            tessellations.insert(id, output);
            return id;
        }
    }
    0
}
```

### 6. Vertex/Index Buffer Access

```rust
#[no_mangle]
pub extern "C" fn rt_lyon_vertex_buffer_size(buffer_id: i64) -> i64 {
    let buffers = VERTEX_BUFFERS.lock().unwrap();
    if let Some(buffer) = buffers.get(&buffer_id) {
        buffer.len() as i64
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_vertex_buffer_get_position(
    buffer_id: i64,
    index: i64,
) -> (f64, f64) {
    let buffers = VERTEX_BUFFERS.lock().unwrap();
    if let Some(buffer) = buffers.get(&buffer_id) {
        if let Some(vertex) = buffer.get(index as usize) {
            return (vertex.position.x as f64, vertex.position.y as f64);
        }
    }
    (0.0, 0.0)
}

#[no_mangle]
pub extern "C" fn rt_lyon_index_buffer_size(buffer_id: i64) -> i64 {
    let buffers = INDEX_BUFFERS.lock().unwrap();
    if let Some(buffer) = buffers.get(&buffer_id) {
        buffer.len() as i64
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_lyon_index_buffer_get(buffer_id: i64, index: i64) -> i64 {
    let buffers = INDEX_BUFFERS.lock().unwrap();
    if let Some(buffer) = buffers.get(&buffer_id) {
        if let Some(&idx) = buffer.get(index as usize) {
            return idx as i64;
        }
    }
    0
}
```

## Integration with Simple Runtime

### Location

Add the implementation to the runtime's FFI module:
- **Path**: `bin/runtime/src/ffi/graphics2d.rs` (new file)
- **Add to**: `bin/runtime/src/ffi/mod.rs`

### Module Structure

```rust
// bin/runtime/src/ffi/mod.rs
pub mod graphics2d;  // Add this

// bin/runtime/src/ffi/graphics2d.rs
mod lyon_ffi;  // The implementation above

pub use lyon_ffi::*;
```

## Testing Strategy

### 1. Unit Tests (Rust)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_builder() {
        let builder_id = rt_lyon_path_builder_new();
        assert!(builder_id > 0);

        assert!(rt_lyon_path_builder_begin(builder_id, 0.0, 0.0));
        assert!(rt_lyon_path_builder_line_to(builder_id, 100.0, 0.0));
        assert!(rt_lyon_path_builder_close(builder_id));

        let path_id = rt_lyon_path_builder_build(builder_id);
        assert!(path_id > 0);

        assert!(rt_lyon_path_free(path_id));
    }

    #[test]
    fn test_circle_tessellation() {
        let path_id = rt_lyon_path_circle(50.0, 50.0, 25.0);
        assert!(path_id > 0);

        let tess_id = rt_lyon_fill_tessellate(path_id, 0.1);
        assert!(tess_id > 0);

        let vertex_count = rt_lyon_fill_tessellation_vertex_count(tess_id);
        assert!(vertex_count > 0);

        let index_count = rt_lyon_fill_tessellation_index_count(tess_id);
        assert!(index_count > 0);
        assert_eq!(index_count % 3, 0); // Must be triangles
    }
}
```

### 2. Integration Tests (Simple)

```bash
bin/simple test test/app/io/graphics2d_ffi_spec.spl
```

### 3. Demo Test

```bash
bin/simple examples/graphics2d_demo.spl
```

## Performance Considerations

### Tessellation Quality vs Performance

```rust
// Lower tolerance = higher quality, more triangles
let high_quality = FillOptions::tolerance(0.01);

// Higher tolerance = lower quality, fewer triangles
let low_quality = FillOptions::tolerance(1.0);
```

**Rule of thumb**:
- UI elements: 0.1 - 0.5
- Icons/logos: 0.01 - 0.1
- Large shapes: 0.5 - 1.0

### Memory Management

```rust
// Reuse tessellation buffers when possible
fn reuse_buffer_pattern() {
    let mut geometry = VertexBuffers::new();

    for path in paths {
        geometry.vertices.clear();
        geometry.indices.clear();

        tessellator.tessellate_path(
            &path,
            &options,
            &mut BuffersBuilder::new(&mut geometry, VertexCtor),
        ).ok();

        // Upload to GPU here
    }
}
```

## Example Implementation Checklist

- [ ] Add `lyon` dependencies to runtime `Cargo.toml`
- [ ] Implement path builder (new, begin, line_to, curves, close, build)
- [ ] Implement shape primitives (rectangle, circle, ellipse, polygon, star)
- [ ] Implement path operations (free, bounds, contains_point)
- [ ] Implement fill tessellation (basic + fill rules)
- [ ] Implement stroke tessellation (basic + options)
- [ ] Implement vertex buffer access (size, get_position, get_normal)
- [ ] Implement index buffer access (size, get)
- [ ] Implement transform operations
- [ ] Add error handling
- [ ] Write Rust unit tests
- [ ] Run Simple integration tests
- [ ] Test demo example
- [ ] Profile tessellation performance

## GPU Integration Example

Lyon produces triangles for GPU rendering:

```rust
// After tessellation, upload to GPU (pseudocode)
fn upload_to_gpu(tess_id: i64) {
    let vertices = get_vertices_array(tess_id);
    let indices = get_indices_array(tess_id);

    // With Vulkan
    vulkan_upload_vertex_buffer(vertices);
    vulkan_upload_index_buffer(indices);

    // With wgpu
    device.create_buffer_init(&BufferInitDescriptor {
        label: Some("Vertex Buffer"),
        contents: bytemuck::cast_slice(&vertices),
        usage: BufferUsages::VERTEX,
    });
}
```

## Next Steps

1. **Implement Core Functions** (~400 lines)
   - Path builder, shape primitives

2. **Implement Tessellation** (~300 lines)
   - Fill and stroke tessellators

3. **Implement Buffers** (~100 lines)
   - Vertex/index buffer access

4. **Implement Utilities** (~100 lines)
   - Transforms, error handling

**Total Estimated**: 800-1000 lines Rust

## Summary

The Simple-side SFFI wrapper is **production-ready** (~700 lines). The Rust implementation requires:

1. **~800-1000 lines** of Rust code
2. **Lyon dependency** (~300KB compiled)
3. **Handle management** for paths, tessellations, buffers
4. **Vertex/Index buffer** conversion

Once implemented, Simple programs can create GPU-ready 2D vector graphics for UI, games, and data visualization.
