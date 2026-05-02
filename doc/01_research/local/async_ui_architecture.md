# Async UI Architecture - JavaScript-Style Futures/Promises

## Overview

Redesign the UI backend to use async/await and Futures/Promises throughout, enabling:
- Non-blocking rendering operations
- Parallel CPU and GPU work
- Better responsiveness
- JavaScript-like async patterns

## Architecture Layers

```
┌────────────────────────────────────────────────────────────────┐
│                    Application Layer                            │
│  async fn update_ui() {                                         │
│    let result = await renderer.render(tree)                     │
│    match result { ... }                                         │
│  }                                                              │
└────────────────────────────────────────────────────────────────┘
                           │ async API
                           ▼
┌────────────────────────────────────────────────────────────────┐
│                 RenderBackend (Async Trait)                     │
│  async fn render(&self, tree: &ElementTree) -> Future<Result>  │
│  async fn apply_patches(&self, patches) -> Future<Result>      │
└────────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌────────────────────────────────────────────────────────────────┐
│              VulkanRenderer (Async Implementation)              │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  CPU Work (Parallel Tasks)                               │  │
│  │  - Task 1: async layout_future = layout_engine.compute() │  │
│  │  - Task 2: async process_future = processor.process()    │  │
│  │  - Task 3: async upload_future = buffer_mgr.upload()     │  │
│  └──────────────────────────────────────────────────────────┘  │
│                           │                                     │
│                           │ await all                           │
│                           ▼                                     │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  GPU Work (Async Submit)                                 │  │
│  │  - Submit command buffer (returns fence future)          │  │
│  │  - GPU executes in parallel                              │  │
│  │  - Future resolves when GPU done                         │  │
│  └──────────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────────┘
                           │
                           ▼
                      GPU Hardware
```

## Async API Design

### RenderBackend Trait (Async)

```simple
# Async render backend trait
trait RenderBackend:
    # Initialize the renderer (async setup)
    async fn init(self) -> Future[Result[(), RenderError]]

    # Shutdown the renderer (async cleanup)
    async fn shutdown(self) -> Future[Result[(), RenderError]]

    # Get screen/window dimensions (sync - just reading state)
    fn dimensions(self) -> (u16, u16)

    # Render an element tree (async - GPU work)
    async fn render(self, tree: &ElementTree) -> Future[Result[(), RenderError]]

    # Apply patches (async - may involve GPU updates)
    async fn apply_patches(self, patches: &PatchSet) -> Future[Result[(), RenderError]]

    # Clear the screen (async - GPU work)
    async fn clear(self) -> Future[Result[(), RenderError]]

    # Flush pending changes (async - wait for GPU)
    async fn flush(self) -> Future[Result[(), RenderError]]

    # Poll event (async - may block on I/O)
    async fn poll_event(self, timeout_ms: u64) -> Future[Result[Option[Event], RenderError]]

    # Read event (async - blocks until event)
    async fn read_event(self) -> Future[Result[Event, RenderError]]
```

### Application Usage (JavaScript-like)

```simple
# Example 1: Simple async rendering
async fn render_app():
    let renderer = VulkanRenderer::new("My App", 800, 600)?
    await renderer.init()

    let tree = create_ui_tree()

    # Non-blocking render
    await renderer.render(&tree)

    await renderer.shutdown()

# Example 2: Parallel operations
async fn update_and_render():
    # Start render in background
    let render_future = renderer.render(&tree)

    # Do other work while rendering
    let data = await fetch_data_from_server()

    # Wait for render to complete
    await render_future

    # Apply updates
    let patches = diff(old_tree, new_tree)
    await renderer.apply_patches(&patches)

# Example 3: Promise.all style (parallel await)
async fn parallel_updates():
    # Start multiple async operations
    let render_future = renderer.render(&tree)
    let data_future = fetch_user_data()
    let analytics_future = send_analytics()

    # Wait for all to complete
    let results = await Future::all([
        render_future,
        data_future,
        analytics_future
    ])

    match results:
        case [Ok(()), Ok(data), Ok(())]:
            # All succeeded
            update_ui_with_data(data)
        case _:
            # Handle errors
            show_error()

# Example 4: Event loop with async
async fn main_loop():
    loop:
        # Non-blocking event poll
        match await renderer.poll_event(16):  # 60 FPS
            case Ok(Some(Event::Key(key))):
                if key.is_escape():
                    break
                # Update UI based on input
                let new_tree = handle_input(key, tree)
                let patches = diff(tree, new_tree)
                await renderer.apply_patches(&patches)
                tree = new_tree
            case Ok(None):
                # No event - render frame
                await renderer.render(&tree)
            case Err(e):
                handle_error(e)
```

## CPU → GPU Async Pipeline

### Frame Rendering (Fully Async)

```simple
async fn render(self, tree: &ElementTree) -> Future[Result[(), RenderError]]:
    # 1. Begin frame (async - acquire swapchain image)
    let frame = await self.begin_frame_async()

    # 2. Spawn parallel CPU tasks
    let layout_future = async { self.layout_engine.compute_layout(tree) }
    let preload_future = async { self.resource_manager.preload_resources(tree) }

    # 3. Wait for layout to complete
    let layout_result = await layout_future

    # 4. Process elements (can start while preload continues)
    let process_future = async {
        self.element_processor.process_tree(tree, &layout_result)
    }

    # 5. Wait for both to complete
    let (draw_list, _) = await Future::join(process_future, preload_future)

    # 6. Upload to GPU (async - returns when upload complete)
    await self.buffer_manager.upload_draw_list_async(&draw_list, frame.buffer_index)

    # 7. Record commands (CPU work, but can be async for parallelism)
    await self.record_commands_async(&frame, &draw_list)

    # 8. Submit to GPU (async - returns immediately, GPU works in parallel)
    let submit_future = self.submit_frame_async(frame)

    # 9. Present (async - waits for GPU completion + vsync)
    await self.present_async(frame, submit_future)

    return Ok(())
```

### Detailed Async Operations

#### 1. Begin Frame (Async)
```simple
async fn begin_frame_async(self) -> Future[Frame]:
    # Wait for previous frame fence (non-blocking)
    let fence = self.frame_data[self.frame_index].fence
    await self.device.wait_for_fence_async(fence)

    # Reset fence for this frame
    self.device.reset_fence(fence)

    # Acquire next swapchain image (async - may wait for vsync)
    let image_index = await self.swapchain.acquire_next_image_async(
        self.frame_data[self.frame_index].image_available
    )

    # Reset command buffer
    let cmd_buf = self.frame_data[self.frame_index].command_buffer
    self.device.reset_command_buffer(cmd_buf)

    return Frame {
        image_index: image_index,
        buffer_index: self.frame_index,
        command_buffer: cmd_buf
    }
```

#### 2. Layout Computation (Async)
```simple
# LayoutEngine - async computation
async fn compute_layout_async(self, elem: &Element, constraints: BoxConstraints)
    -> Future[LayoutResult]:
    # Check cache (fast path)
    if let Some(cached) = self.cache.get(elem.id):
        if cached.constraints == constraints:
            return Future::ready(cached.result)

    # For complex layouts, spawn parallel tasks for children
    let children_futures: Array[Future[LayoutResult]] = []

    for child in &elem.children:
        let child_constraints = self.compute_child_constraints(child, constraints)
        # Spawn async task for each child
        let future = async { self.compute_layout_async(child, child_constraints) }
        children_futures.push(future)

    # Wait for all children in parallel
    let children_results = await Future::all(children_futures)

    # Combine results
    let result = self.combine_layout_results(elem, children_results)

    # Cache and return
    self.cache.set(elem.id, constraints, result)
    return result
```

#### 3. Buffer Upload (Async)
```simple
# BufferManager - async uploads
async fn upload_draw_list_async(self, draw_list: &DrawList, frame_index: usize)
    -> Future[()]:
    # Get or allocate buffers
    let vertex_buffer = self.get_or_allocate_vertex_buffer(
        draw_list.vertices.len(),
        frame_index
    )
    let index_buffer = self.get_or_allocate_index_buffer(
        draw_list.indices.len(),
        frame_index
    )

    # Upload vertex data (async - may use DMA)
    let vertex_upload = async {
        self.device.upload_to_buffer_async(
            vertex_buffer,
            draw_list.vertices.as_bytes()
        )
    }

    # Upload index data (async - may use DMA)
    let index_upload = async {
        self.device.upload_to_buffer_async(
            index_buffer,
            draw_list.indices.as_bytes()
        )
    }

    # Wait for both uploads to complete
    await Future::join(vertex_upload, index_upload)
```

#### 4. Command Recording (Async for Parallelism)
```simple
# Record commands - async to enable parallel recording
async fn record_commands_async(self, frame: &Frame, draw_list: &DrawList)
    -> Future[()]:
    # Secondary command buffers can be recorded in parallel
    let secondary_cmd_bufs = self.allocate_secondary_command_buffers(
        draw_list.draw_calls.len()
    )

    # Record each draw call in parallel
    let record_futures: Array[Future[()]] = []

    for (i, draw_call) in draw_list.draw_calls.enumerate():
        let cmd_buf = secondary_cmd_bufs[i]
        let future = async {
            self.record_draw_call(cmd_buf, draw_call)
        }
        record_futures.push(future)

    # Wait for all recordings to complete
    await Future::all(record_futures)

    # Record primary command buffer (executes secondaries)
    let cmd_buf = frame.command_buffer
    self.begin_primary_command_buffer(cmd_buf)
    self.begin_render_pass(cmd_buf, frame.image_index)

    for secondary in secondary_cmd_bufs:
        self.execute_secondary_command_buffer(cmd_buf, secondary)

    self.end_render_pass(cmd_buf)
    self.end_command_buffer(cmd_buf)
```

#### 5. Submit to GPU (Async)
```simple
# Submit frame - returns future that resolves when GPU done
async fn submit_frame_async(self, frame: Frame) -> Future[GpuSubmitResult]:
    let submit_info = VkSubmitInfo {
        wait_semaphores: [self.frame_data[frame.buffer_index].image_available],
        command_buffers: [frame.command_buffer],
        signal_semaphores: [self.frame_data[frame.buffer_index].render_finished],
        fence: self.frame_data[frame.buffer_index].fence
    }

    # Submit to queue (non-blocking - GPU executes in parallel)
    self.device.queue_submit_async(submit_info)

    # Return future that completes when fence is signaled
    return self.device.create_fence_future(self.frame_data[frame.buffer_index].fence)
```

#### 6. Present (Async)
```simple
# Present frame - waits for GPU + vsync
async fn present_async(self, frame: Frame, gpu_future: Future[GpuSubmitResult])
    -> Future[Result[(), RenderError]]:
    # Wait for GPU to finish rendering
    await gpu_future

    # Present to swapchain (async - may wait for vsync)
    let present_info = VkPresentInfo {
        wait_semaphores: [self.frame_data[frame.buffer_index].render_finished],
        swapchains: [self.swapchain.swapchain],
        image_indices: [frame.image_index]
    }

    let result = await self.device.queue_present_async(present_info)

    # Advance frame index
    self.frame_index = (self.frame_index + 1) % 3

    return result
```

## Patch Application (Async)

```simple
async fn apply_patches_async(self, patches: &PatchSet) -> Future[Result[(), RenderError]]:
    # 1. Identify affected regions (CPU work)
    let dirty_regions = self.compute_dirty_regions(patches)

    # 2. Partial re-layout (async, parallel for each dirty region)
    let layout_futures = dirty_regions.map(|region| async {
        self.layout_engine.recompute_region(region)
    })
    let layout_results = await Future::all(layout_futures)

    # 3. Regenerate draw list for dirty regions only
    let process_future = async {
        self.element_processor.process_dirty_regions(&layout_results)
    }
    let partial_draw_list = await process_future

    # 4. Upload updated geometry (async)
    await self.buffer_manager.update_partial_async(
        &partial_draw_list,
        dirty_regions
    )

    # 5. Re-record only affected command buffers
    await self.record_partial_commands_async(&partial_draw_list, &dirty_regions)

    return Ok(())
```

## Async Event Handling

```simple
# Event polling - async to avoid blocking
async fn poll_event_async(self, timeout_ms: u64) -> Future[Result[Option[Event], RenderError]]:
    # Create a future that completes when event arrives or timeout
    let event_future = self.window.poll_event_future(timeout_ms)

    # Can race with timeout
    let result = await Future::race([
        event_future,
        async {
            sleep_async(timeout_ms).await
            Ok(None)
        }
    ])

    return result

# Event loop - async generator/stream
async fn event_stream(self) -> AsyncStream[Event]:
    loop:
        match await self.poll_event_async(u64::MAX):
            case Ok(Some(event)):
                yield event
            case Ok(None):
                break
            case Err(e):
                yield Event::Error(e)
                break

# Usage
async fn handle_events():
    let stream = renderer.event_stream()
    for await event in stream:
        match event:
            case Event::Key(key):
                handle_key(key)
            case Event::Mouse(mouse):
                handle_mouse(mouse)
            case Event::Resize { width, height }:
                await renderer.resize_async(width, height)
```

## Resource Loading (Async)

```simple
# ResourceManager - async loading
async fn load_texture_async(self, path: &str) -> Future[Result[TextureId, String]]:
    # Read file asynchronously
    let image_data = await fs::read_async(path)

    # Decode image (CPU-bound, spawn on thread pool)
    let decoded = await spawn_blocking(|| {
        decode_image(&image_data)
    })

    # Upload to GPU (async)
    let texture = await self.device.create_texture_async(
        decoded.width,
        decoded.height,
        decoded.data
    )

    # Cache and return
    let texture_id = self.next_texture_id
    self.next_texture_id = self.next_texture_id + 1
    self.textures.set(texture_id, texture)

    return Ok(texture_id)

# Preload resources in parallel
async fn preload_resources_async(self, tree: &ElementTree) -> Future[()]:
    let load_futures: Array[Future[Result[TextureId, String>]] = []

    # Traverse tree and collect resources to load
    for elem in tree.iter():
        if let Some(src) = elem.attrs.get("src"):
            if not self.is_loaded(src):
                let future = self.load_texture_async(src)
                load_futures.push(future)

    # Load all in parallel
    let results = await Future::all(load_futures)

    # Handle any load failures
    for result in results:
        match result:
            case Err(e):
                log_error(f"Failed to load resource: {e}")
            case Ok(_):
                pass
```

## Synchronization Primitives

### Future Combinators

```simple
# Future::all - wait for all futures to complete (like Promise.all)
pub fn all<T>(futures: Array[Future[T]]) -> Future[Array[T]]:
    # Returns future that completes when all input futures complete
    # Result is array of all results

# Future::race - wait for first future to complete (like Promise.race)
pub fn race<T>(futures: Array[Future[T]]) -> Future[T]:
    # Returns future that completes when first input future completes
    # Result is the result of the winning future

# Future::join - wait for two futures in parallel
pub fn join<T, U>(fut1: Future[T], fut2: Future[U]) -> Future[(T, U)]:
    # Returns future that completes when both complete
    # Result is tuple of both results

# Future::ready - create immediately-completed future
pub fn ready<T>(value: T) -> Future[T]:
    # Returns future that is already completed with value

# Future::pending - create never-completing future
pub fn pending<T>() -> Future[T]:
    # Returns future that never completes (useful for timeouts)
```

### Async Utilities

```simple
# Sleep asynchronously
async fn sleep_async(ms: u64) -> Future[()]:
    # Non-blocking sleep
    # Uses OS timer or event loop

# Spawn blocking task on thread pool
async fn spawn_blocking<T>(f: fn() -> T) -> Future[T]:
    # Runs CPU-bound work on thread pool
    # Returns future that completes when work done

# Timeout wrapper
async fn timeout<T>(future: Future[T], ms: u64) -> Future[Result[T, TimeoutError]]:
    let result = await Future::race([
        future.map(|v| Ok(v)),
        sleep_async(ms).map(|_| Err(TimeoutError))
    ])
    return result
```

## Performance Benefits

### 1. CPU-GPU Parallelism
```
Without Async (Sequential):
├─ CPU: Layout     [═══════════]
├─ CPU: Process               [═══════════]
├─ CPU: Upload                           [═══════]
└─ GPU: Render                                  [═══════════════]
   Total time: ~40ms

With Async (Parallel):
├─ CPU: Layout     [═══════════]
├─ CPU: Process               [═══════════]
├─ CPU: Upload                           [═══]
└─ GPU: Render                  [═══════════════]
   Total time: ~25ms (37% faster!)
```

### 2. Multi-threaded Layout
```
Without Async (Single-threaded):
└─ Layout: [════════════════════════════] 20ms

With Async (4 cores):
├─ Layout Child 1: [═════]
├─ Layout Child 2: [═════]
├─ Layout Child 3: [═════]
└─ Layout Child 4: [═════]
   Total time: ~5ms (4x faster!)
```

### 3. Overlapped Resource Loading
```
Without Async (Sequential):
├─ Load Texture 1: [════]
├─ Load Texture 2:     [════]
├─ Load Texture 3:         [════]
└─ Load Texture 4:             [════]
   Total time: 16ms

With Async (Parallel):
├─ Load Texture 1: [════]
├─ Load Texture 2: [════]
├─ Load Texture 3: [════]
└─ Load Texture 4: [════]
   Total time: 4ms (4x faster!)
```

## Error Handling

Simple uses Result-based error handling (no try/catch). This makes error paths explicit in the type system.

```simple
# Result-based async error handling
async fn render_with_result() -> Result<void, RenderError>:
    await renderer.init()?

    loop:
        match await renderer.render(&tree):
            case Ok(()):
                # Success - continue rendering
                pass
            case Err(RenderError::DeviceLost):
                # GPU reset - recreate resources
                await renderer.recreate_swapchain()?
            case Err(RenderError::SwapchainOutOfDate):
                # Window resized - recreate swapchain
                await renderer.recreate_swapchain()?
                await renderer.render(&tree)?  # Retry
            case Err(RenderError::OutOfMemory):
                # Free some resources
                await resource_manager.cleanup_unused()
            case Err(e):
                return Err(e)

    await renderer.shutdown()
    return Ok(())
```

## Async State Machine (Under the Hood)

```simple
# What the compiler generates for:
async fn render(self, tree: &ElementTree) -> Future[Result[(), RenderError]]:
    let frame = await self.begin_frame_async()
    let layout = await self.layout_engine.compute_layout(tree)
    return Ok(())

# Becomes:
enum RenderStateMachine:
    Start
    WaitingForFrame { tree: ElementTree }
    WaitingForLayout { frame: Frame, tree: ElementTree }
    Done { result: Result[(), RenderError] }

impl Future for RenderStateMachine:
    fn poll(self) -> Poll[Result[(), RenderError]]:
        match self:
            case Start:
                let frame_future = self.begin_frame_async()
                if frame_future.is_ready():
                    let frame = frame_future.get()
                    self = WaitingForLayout { frame, tree }
                    return Poll::Pending
                else:
                    self = WaitingForFrame { tree }
                    return Poll::Pending

            case WaitingForFrame { tree }:
                let frame_future = self.begin_frame_async()
                if frame_future.is_ready():
                    let frame = frame_future.get()
                    self = WaitingForLayout { frame, tree }
                    return self.poll()  # Continue immediately
                return Poll::Pending

            case WaitingForLayout { frame, tree }:
                let layout_future = self.layout_engine.compute_layout(tree)
                if layout_future.is_ready():
                    self = Done { result: Ok(()) }
                    return self.poll()
                return Poll::Pending

            case Done { result }:
                return Poll::Ready(result)
```

## Reactor/Runtime

```simple
# Async runtime for executing futures
pub struct AsyncRuntime:
    task_queue: TaskQueue
    waker_registry: WakerRegistry
    thread_pool: ThreadPool

impl AsyncRuntime:
    pub fn new() -> AsyncRuntime:
        return AsyncRuntime {
            task_queue: TaskQueue::new(),
            waker_registry: WakerRegistry::new(),
            thread_pool: ThreadPool::new(num_cpus())
        }

    # Block until future completes
    pub fn block_on<T>(self, future: Future[T]) -> T:
        let waker = self.waker_registry.create_waker()
        let mut future = future

        loop:
            match future.poll(waker):
                case Poll::Ready(value):
                    return value
                case Poll::Pending:
                    # Park thread until waker is called
                    self.task_queue.park()

    # Spawn future on runtime
    pub fn spawn<T>(self, future: Future[T]) -> JoinHandle[T]:
        let task = Task::new(future)
        self.task_queue.push(task)
        return JoinHandle::new(task.id)
```

## Integration with Existing Code

```simple
# Migration path: wrap sync functions in async
fn compute_layout_sync(elem: &Element) -> LayoutResult:
    # Old synchronous code
    ...

async fn compute_layout_async(elem: &Element) -> Future[LayoutResult]:
    # Wrap in async to enable future composition
    return Future::ready(compute_layout_sync(elem))

# Then gradually replace with true async implementations
async fn compute_layout_async_v2(elem: &Element) -> Future[LayoutResult]:
    # True async implementation with parallelism
    let children_futures = elem.children.map(|c| async {
        compute_layout_async_v2(c)
    })
    let children_results = await Future::all(children_futures)
    return combine_results(elem, children_results)
```

## Summary

The async architecture provides:

1. **Non-blocking API**: Application never blocks on rendering
2. **CPU-GPU Parallelism**: CPU prepares next frame while GPU renders current
3. **Multi-threaded CPU**: Layout and processing can use all CPU cores
4. **Resource Loading**: Images/fonts load in parallel
5. **Better Responsiveness**: UI stays responsive during heavy operations
6. **JavaScript-like**: Familiar async/await patterns from web development
7. **Composable**: Futures can be combined with `all`, `race`, `join`
8. **Error Handling**: Clear error propagation with Result types

This makes the UI framework suitable for:
- Interactive applications with smooth 60+ FPS
- Games with complex UI
- Data visualization with large datasets
- Real-time collaborative apps
- Any application requiring responsive UI
