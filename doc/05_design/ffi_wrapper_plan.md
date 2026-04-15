# FFI Wrapper Generation Plan

## Overview

Generate complete FFI wrappers for all Rust libraries used in Simple v0.3.0, organized as a multi-crate workspace. Each crate maps to a specific domain and is consumed by Simple packages.

## Architecture

```
build/rust/
├── Cargo.toml                    # Workspace root
├── rust-toolchain.toml           # Toolchain config (from simple.sdn)
│
├── ffi_core/                     # Core runtime (GC, memory, types)
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── gc.rs                 # bdwgc-alloc wrapper
│       ├── memory.rs             # Memory allocation
│       └── types.rs              # RuntimeValue, basic types
│
├── ffi_io/                       # File, Directory, Environment
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── file.rs               # std::fs wrapper
│       ├── dir.rs                # Directory operations
│       ├── env.rs                # std::env wrapper
│       ├── path.rs               # std::path wrapper
│       └── glob.rs               # glob crate wrapper
│
├── ffi_process/                  # Process execution, shell
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── process.rs            # std::process wrapper
│       ├── shell.rs              # Shell execution
│       └── sandbox.rs            # Resource limits (rlimit, nix)
│
├── ffi_time/                     # Time operations
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── time.rs               # std::time wrapper
│       ├── timestamp.rs          # Date/time parsing
│       └── chrono.rs             # chrono crate wrapper
│
├── ffi_crypto/                   # Cryptographic operations
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── sha.rs                # sha1, sha2 wrapper
│       ├── hash.rs               # xxhash, ahash wrapper
│       └── argon2.rs             # Password hashing
│
├── ffi_archive/                  # Archive/compression
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── tar.rs                # tar crate wrapper
│       ├── gzip.rs               # flate2 wrapper
│       └── xz.rs                 # xz2/lzma wrapper
│
├── ffi_codegen/                  # JIT/AOT compilation
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── cranelift.rs          # Cranelift wrapper
│       └── target.rs             # target-lexicon wrapper
│
├── ffi_net/                      # Networking (optional)
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── socket.rs             # socket2 wrapper
│       ├── http.rs               # ureq wrapper
│       └── tcp.rs                # TCP operations
│
├── ffi_concurrent/               # Concurrency primitives
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── thread.rs             # std::thread wrapper
│       ├── sync.rs               # parking_lot wrapper
│       ├── channel.rs            # crossbeam wrapper
│       └── parallel.rs           # rayon wrapper
│
├── ffi_data/                     # Data structures
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── arena.rs              # typed-arena wrapper
│       ├── intern.rs             # lasso string interning
│       ├── collections.rs        # dashmap, indexmap wrapper
│       └── regex.rs              # regex crate wrapper
│
├── ffi_system/                   # System info
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── hostname.rs           # hostname crate wrapper
│       ├── cpu.rs                # num_cpus, sysinfo wrapper
│       └── platform.rs           # Platform detection
│
├── ffi_cli/                      # CLI utilities
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── args.rs               # Argument parsing
│       ├── repl.rs               # rustyline wrapper
│       ├── watch.rs              # notify wrapper
│       └── signal.rs             # ctrlc wrapper
│
├── ffi_serde/                    # Serialization
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── json.rs               # serde_json wrapper
│       ├── toml.rs               # toml wrapper
│       ├── yaml.rs               # serde_yaml wrapper
│       └── bincode.rs            # bincode wrapper
│
├── ffi_torch/                    # PyTorch/ML (optional)
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── tensor.rs             # tch tensor wrapper
│       ├── autograd.rs           # Automatic differentiation
│       ├── nn.rs                 # Neural network layers
│       ├── optim.rs              # Optimizers (SGD, Adam)
│       ├── data.rs               # DataLoader, Dataset
│       └── device.rs             # CPU/CUDA device selection
│
├── ffi_cuda/                     # CUDA Runtime (optional)
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── device.rs             # CUDA device management
│       ├── memory.rs             # CUDA memory allocation
│       ├── kernel.rs             # Kernel launching
│       └── stream.rs             # CUDA streams
│
└── ffi_vulkan/                   # Vulkan GPU (optional)
    ├── Cargo.toml
    └── src/
        ├── lib.rs
        ├── instance.rs           # ash instance wrapper
        ├── device.rs             # Logical/physical device
        ├── buffer.rs             # GPU buffers
        ├── compute.rs            # Compute pipelines
        ├── graphics.rs           # Graphics pipelines
        └── spirv.rs              # SPIR-V shader loading
```

## Crate Dependencies

```
┌─────────────────────────────────────────────────────────────────┐
│                        Simple Packages                          │
│  (build, test_runner, cli, formatter, lint, package, etc.)     │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     src/app/io/mod.spl                          │
│                  (extern fn declarations)                       │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   build/rust/ workspace                         │
│                                                                 │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐       │
│  │ ffi_core │  │ ffi_io   │  │ffi_process│ │ ffi_time │       │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘       │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐       │
│  │ffi_crypto│  │ffi_archive│ │ffi_codegen│ │ ffi_net  │       │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘       │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐       │
│  │ffi_concur│  │ ffi_data │  │ffi_system│  │ ffi_cli  │       │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘       │
│  ┌──────────┐                                                  │
│  │ffi_serde │                                                  │
│  └──────────┘                                                  │
│                                                                 │
│  ┌─────────────────── OPTIONAL (feature flags) ──────────────┐ │
│  │ ┌──────────┐  ┌──────────┐  ┌──────────┐                  │ │
│  │ │ffi_torch │  │ ffi_cuda │  │ffi_vulkan│                  │ │
│  │ │ (tch)    │  │ (cuda)   │  │ (ash)    │                  │ │
│  │ └──────────┘  └──────────┘  └──────────┘                  │ │
│  └───────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Rust Crates (crates.io)                     │
│  libc, glob, hostname, sha2, tar, flate2, cranelift, etc.      │
└─────────────────────────────────────────────────────────────────┘
```

## Phase 1: Core Infrastructure (Priority: Critical)

### 1.1 ffi_core - Core Runtime
**Rust libs:** `bdwgc-alloc`, `libc`
**Simple packages:** ALL

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_gc_init` | `bdwgc_alloc::Allocator::init()` | TODO |
| `rt_gc_malloc` | `GC_MALLOC` | TODO |
| `rt_gc_free` | `GC_FREE` | TODO |
| `rt_gc_collect` | `GC_gcollect()` | TODO |
| `rt_gc_disable` | `GC_disable()` | TODO |
| `rt_gc_enable` | `GC_enable()` | TODO |
| `rt_gc_stats` | Memory statistics | TODO |

### 1.2 ffi_io - File/Directory/Environment
**Rust libs:** `std::fs`, `std::env`, `std::path`, `glob`, `dirs-next`, `memmap2`, `fs2`
**Simple packages:** build, cli, test_runner, formatter, lint, fix, package, init, watch, cache, lock

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_file_exists` | `Path::exists()` | DONE |
| `rt_file_read_text` | `fs::read_to_string()` | DONE |
| `rt_file_write_text` | `fs::write()` | DONE |
| `rt_file_copy` | `fs::copy()` | DONE |
| `rt_file_delete` | `fs::remove_file()` | DONE |
| `rt_file_append_text` | `OpenOptions::append()` | DONE |
| `rt_file_atomic_write` | Write tmp + rename | DONE |
| `rt_file_modified_time` | `metadata().modified()` | DONE |
| `rt_file_size` | `metadata().len()` | DONE |
| `rt_file_hash_sha256` | `sha2::Sha256` | DONE |
| `rt_file_lock` | `fs2::FileExt::lock_exclusive()` | TODO (stub) |
| `rt_file_unlock` | `fs2::FileExt::unlock()` | TODO (stub) |
| `rt_file_mmap_read` | `memmap2::Mmap` | TODO |
| `rt_dir_create` | `fs::create_dir()` | DONE |
| `rt_dir_create_all` | `fs::create_dir_all()` | DONE |
| `rt_dir_list` | `fs::read_dir()` | DONE |
| `rt_dir_walk` | Recursive read_dir | DONE |
| `rt_dir_remove` | `fs::remove_dir()` | DONE |
| `rt_dir_remove_all` | `fs::remove_dir_all()` | DONE |
| `rt_env_cwd` | `env::current_dir()` | DONE |
| `rt_env_home` | `dirs_next::home_dir()` | DONE |
| `rt_env_get` | `env::var()` | DONE |
| `rt_env_set` | `env::set_var()` | DONE |
| `rt_path_basename` | `Path::file_name()` | DONE |
| `rt_path_dirname` | `Path::parent()` | TODO |
| `rt_path_join` | `Path::join()` | TODO |
| `rt_path_exists` | `Path::exists()` | DONE |
| `rt_glob` | `glob::glob()` | DONE |

### 1.3 ffi_process - Process Execution
**Rust libs:** `std::process`, `nix`, `rlimit`
**Simple packages:** build, cli, test_runner, run, compile, watch

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_process_run` | `Command::output()` | DONE |
| `rt_process_run_timeout` | Command + timeout | DONE (stub) |
| `rt_process_run_with_limits` | nix + rlimit | DONE (stub) |
| `rt_process_spawn` | `Command::spawn()` | TODO |
| `rt_process_kill` | `Child::kill()` | TODO |
| `rt_process_wait` | `Child::wait()` | TODO |
| `rt_shell` | `sh -c` | DONE |
| `rt_shell_exec` | `sh -c` + exit code | DONE |
| `rt_getpid` | `process::id()` | DONE |
| `rt_sandbox_set_limits` | rlimit | TODO |

### 1.4 ffi_time - Time Operations
**Rust libs:** `std::time`, `chrono`
**Simple packages:** build, test_runner, coverage, todo_scan, feature_gen

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_time_now_unix_micros` | `SystemTime::now()` | DONE |
| `rt_current_time_ms` | `SystemTime::now()` | DONE |
| `rt_timestamp_get_year` | Custom calculation | DONE |
| `rt_timestamp_get_month` | Custom calculation | DONE |
| `rt_timestamp_get_day` | Custom calculation | DONE |
| `rt_timestamp_get_hour` | Custom calculation | DONE |
| `rt_timestamp_get_minute` | Custom calculation | DONE |
| `rt_timestamp_get_second` | Custom calculation | DONE |
| `rt_time_format_iso8601` | chrono | TODO |
| `rt_time_parse_iso8601` | chrono | TODO |

## Phase 2: Build System Support (Priority: High)

### 2.1 ffi_crypto - Cryptographic Operations
**Rust libs:** `sha1`, `sha2`, `xxhash-rust`, `ahash`, `argon2`
**Simple packages:** cache, lock, build, qualify_ignore

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_sha256_hash` | `sha2::Sha256` | DONE |
| `rt_sha1_hash` | `sha1::Sha1` | TODO |
| `rt_xxhash64` | `xxhash_rust::xxh64` | TODO |
| `rt_xxhash3` | `xxhash_rust::xxh3` | TODO |
| `rt_ahash` | `ahash::AHasher` | TODO |
| `rt_argon2_hash` | `argon2::hash_encoded` | TODO |
| `rt_argon2_verify` | `argon2::verify_encoded` | TODO |

### 2.2 ffi_archive - Archive/Compression
**Rust libs:** `tar`, `flate2`, `xz2`
**Simple packages:** package, release, install

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_tar_create` | `tar::Builder` | TODO |
| `rt_tar_extract` | `tar::Archive::unpack()` | TODO |
| `rt_tar_list` | `tar::Archive::entries()` | TODO |
| `rt_gzip_compress` | `flate2::write::GzEncoder` | TODO |
| `rt_gzip_decompress` | `flate2::read::GzDecoder` | TODO |
| `rt_xz_compress` | `xz2::write::XzEncoder` | TODO |
| `rt_xz_decompress` | `xz2::read::XzDecoder` | TODO |

### 2.3 ffi_system - System Information
**Rust libs:** `hostname`, `num_cpus`, `sysinfo`
**Simple packages:** build, test_runner

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_hostname` | `hostname::get()` | DONE |
| `rt_cpu_count` | `num_cpus::get()` | DONE |
| `rt_cpu_physical_count` | `num_cpus::get_physical()` | TODO |
| `rt_memory_total` | `sysinfo::System` | TODO |
| `rt_memory_available` | `sysinfo::System` | TODO |
| `rt_os_name` | Platform detection | TODO |
| `rt_arch_name` | Platform detection | TODO |

## Phase 3: Compiler Support (Priority: High)

### 3.1 ffi_codegen - JIT/AOT Compilation
**Rust libs:** `cranelift-*`, `target-lexicon`
**Simple packages:** compile, cli

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_cranelift_init` | Module creation | DONE |
| `rt_cranelift_compile_fn` | FunctionBuilder | DONE |
| `rt_cranelift_emit_object` | ObjectModule::finish() | DONE |
| `rt_cranelift_jit_execute` | JIT execution | TODO |
| `rt_target_triple` | `target_lexicon::Triple` | TODO |
| `rt_target_features` | Target features | TODO |

## Phase 4: Data & Serialization (Priority: Medium)

### 4.1 ffi_data - Data Structures
**Rust libs:** `regex`, `lasso`, `typed-arena`, `dashmap`, `indexmap`, `smallvec`
**Simple packages:** parser, compiler, lint, formatter

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_regex_new` | `Regex::new()` | TODO |
| `rt_regex_is_match` | `Regex::is_match()` | TODO |
| `rt_regex_find` | `Regex::find()` | TODO |
| `rt_regex_captures` | `Regex::captures()` | TODO |
| `rt_intern_string` | `lasso::Rodeo::get_or_intern()` | TODO |
| `rt_intern_resolve` | `lasso::Rodeo::resolve()` | TODO |
| `rt_arena_alloc` | `typed_arena::Arena::alloc()` | TODO |

### 4.2 ffi_serde - Serialization
**Rust libs:** `serde_json`, `toml`, `serde_yaml`, `bincode`
**Simple packages:** sdn, config, package

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_json_parse` | `serde_json::from_str()` | TODO |
| `rt_json_stringify` | `serde_json::to_string()` | TODO |
| `rt_toml_parse` | `toml::from_str()` | TODO |
| `rt_toml_stringify` | `toml::to_string()` | TODO |
| `rt_yaml_parse` | `serde_yaml::from_str()` | TODO |
| `rt_bincode_encode` | `bincode::serialize()` | TODO |
| `rt_bincode_decode` | `bincode::deserialize()` | TODO |

## Phase 5: Concurrency (Priority: Medium)

### 5.1 ffi_concurrent - Concurrency Primitives
**Rust libs:** `rayon`, `crossbeam`, `parking_lot`, `dashmap`
**Simple packages:** build, test_runner, compiler

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_thread_spawn` | `std::thread::spawn()` | TODO |
| `rt_thread_join` | `JoinHandle::join()` | TODO |
| `rt_mutex_new` | `parking_lot::Mutex::new()` | TODO |
| `rt_mutex_lock` | `Mutex::lock()` | TODO |
| `rt_mutex_unlock` | Drop guard | TODO |
| `rt_rwlock_new` | `parking_lot::RwLock::new()` | TODO |
| `rt_channel_create` | `crossbeam::channel::bounded()` | TODO |
| `rt_channel_send` | `Sender::send()` | TODO |
| `rt_channel_recv` | `Receiver::recv()` | TODO |
| `rt_parallel_map` | `rayon::par_iter().map()` | TODO |
| `rt_parallel_for_each` | `rayon::par_iter().for_each()` | TODO |

## Phase 6: GPU & ML (Priority: Optional)

### 6.1 ffi_torch - PyTorch/ML Operations
**Rust libs:** `tch` (libtorch bindings)
**Simple packages:** lms, deeplearning, math
**Feature flag:** `pytorch`

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_tensor_zeros` | `Tensor::zeros()` | TODO |
| `rt_tensor_ones` | `Tensor::ones()` | TODO |
| `rt_tensor_randn` | `Tensor::randn()` | TODO |
| `rt_tensor_from_data` | `Tensor::of_slice()` | TODO |
| `rt_tensor_shape` | `Tensor::size()` | TODO |
| `rt_tensor_dtype` | `Tensor::kind()` | TODO |
| `rt_tensor_device` | `Tensor::device()` | TODO |
| `rt_tensor_to_device` | `Tensor::to_device()` | TODO |
| `rt_tensor_add` | `Tensor::add()` | TODO |
| `rt_tensor_sub` | `Tensor::sub()` | TODO |
| `rt_tensor_mul` | `Tensor::mul()` | TODO |
| `rt_tensor_div` | `Tensor::div()` | TODO |
| `rt_tensor_matmul` | `Tensor::matmul()` | TODO |
| `rt_tensor_transpose` | `Tensor::transpose()` | TODO |
| `rt_tensor_reshape` | `Tensor::reshape()` | TODO |
| `rt_tensor_sum` | `Tensor::sum()` | TODO |
| `rt_tensor_mean` | `Tensor::mean()` | TODO |
| `rt_tensor_backward` | `Tensor::backward()` | TODO |
| `rt_tensor_grad` | `Tensor::grad()` | TODO |
| `rt_tensor_requires_grad` | `Tensor::set_requires_grad()` | TODO |
| `rt_nn_linear` | `nn::linear()` | TODO |
| `rt_nn_conv2d` | `nn::conv2d()` | TODO |
| `rt_nn_relu` | `Tensor::relu()` | TODO |
| `rt_nn_sigmoid` | `Tensor::sigmoid()` | TODO |
| `rt_nn_softmax` | `Tensor::softmax()` | TODO |
| `rt_nn_dropout` | `Tensor::dropout()` | TODO |
| `rt_nn_batch_norm` | `nn::batch_norm2d()` | TODO |
| `rt_nn_layer_norm` | `nn::layer_norm()` | TODO |
| `rt_optim_sgd` | `nn::Sgd` | TODO |
| `rt_optim_adam` | `nn::Adam` | TODO |
| `rt_optim_step` | `Optimizer::step()` | TODO |
| `rt_optim_zero_grad` | `Optimizer::zero_grad()` | TODO |
| `rt_dataloader_new` | Custom iterator | TODO |
| `rt_dataloader_next` | Iterator::next() | TODO |
| `rt_model_save` | `VarStore::save()` | TODO |
| `rt_model_load` | `VarStore::load()` | TODO |

### 6.2 ffi_cuda - CUDA Runtime
**Rust libs:** Custom CUDA bindings (cuda-sys or similar)
**Simple packages:** gpu, deeplearning
**Feature flag:** `cuda`

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_cuda_device_count` | `cudaGetDeviceCount()` | TODO |
| `rt_cuda_device_get` | `cudaGetDevice()` | TODO |
| `rt_cuda_device_set` | `cudaSetDevice()` | TODO |
| `rt_cuda_device_name` | `cudaGetDeviceProperties()` | TODO |
| `rt_cuda_device_memory` | `cudaMemGetInfo()` | TODO |
| `rt_cuda_malloc` | `cudaMalloc()` | TODO |
| `rt_cuda_free` | `cudaFree()` | TODO |
| `rt_cuda_memcpy_h2d` | `cudaMemcpy()` Host→Device | TODO |
| `rt_cuda_memcpy_d2h` | `cudaMemcpy()` Device→Host | TODO |
| `rt_cuda_memcpy_d2d` | `cudaMemcpy()` Device→Device | TODO |
| `rt_cuda_stream_create` | `cudaStreamCreate()` | TODO |
| `rt_cuda_stream_sync` | `cudaStreamSynchronize()` | TODO |
| `rt_cuda_stream_destroy` | `cudaStreamDestroy()` | TODO |
| `rt_cuda_event_create` | `cudaEventCreate()` | TODO |
| `rt_cuda_event_record` | `cudaEventRecord()` | TODO |
| `rt_cuda_event_sync` | `cudaEventSynchronize()` | TODO |
| `rt_cuda_event_elapsed` | `cudaEventElapsedTime()` | TODO |
| `rt_cuda_launch_kernel` | Kernel launch | TODO |

### 6.3 ffi_vulkan - Vulkan GPU Compute/Graphics
**Rust libs:** `ash`, `gpu-allocator`, `spirv-reflect`, `ash-window`, `winit`
**Simple packages:** gpu, graphics, game
**Feature flag:** `vulkan`

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_vk_instance_create` | `Instance::create()` | TODO |
| `rt_vk_instance_destroy` | `Instance::destroy()` | TODO |
| `rt_vk_physical_devices` | `enumerate_physical_devices()` | TODO |
| `rt_vk_device_create` | `Device::create()` | TODO |
| `rt_vk_device_destroy` | `Device::destroy()` | TODO |
| `rt_vk_queue_get` | `Device::get_device_queue()` | TODO |
| `rt_vk_buffer_create` | `Device::create_buffer()` | TODO |
| `rt_vk_buffer_destroy` | `Device::destroy_buffer()` | TODO |
| `rt_vk_memory_allocate` | `gpu_allocator::Allocator` | TODO |
| `rt_vk_memory_free` | `Allocator::free()` | TODO |
| `rt_vk_memory_map` | `Device::map_memory()` | TODO |
| `rt_vk_memory_unmap` | `Device::unmap_memory()` | TODO |
| `rt_vk_shader_load` | `Device::create_shader_module()` | TODO |
| `rt_vk_pipeline_compute` | Compute pipeline | TODO |
| `rt_vk_pipeline_graphics` | Graphics pipeline | TODO |
| `rt_vk_command_pool` | `Device::create_command_pool()` | TODO |
| `rt_vk_command_buffer` | `allocate_command_buffers()` | TODO |
| `rt_vk_command_begin` | `begin_command_buffer()` | TODO |
| `rt_vk_command_end` | `end_command_buffer()` | TODO |
| `rt_vk_dispatch` | `cmd_dispatch()` | TODO |
| `rt_vk_submit` | `queue_submit()` | TODO |
| `rt_vk_fence_wait` | `wait_for_fences()` | TODO |
| `rt_vk_swapchain_create` | Swapchain | TODO |
| `rt_vk_present` | `queue_present()` | TODO |
| `rt_vk_window_create` | `winit::Window` | TODO |
| `rt_vk_surface_create` | `ash_window::create_surface()` | TODO |

## Phase 7: CLI & Networking (Priority: Low)

### 6.1 ffi_cli - CLI Utilities
**Rust libs:** `rustyline`, `notify`, `ctrlc`, `rpassword`
**Simple packages:** repl, watch, qualify_ignore

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_readline` | `rustyline::Editor::readline()` | TODO |
| `rt_readline_add_history` | `Editor::add_history_entry()` | TODO |
| `rt_watch_path` | `notify::Watcher::watch()` | TODO |
| `rt_watch_poll` | Poll for events | TODO |
| `rt_signal_handler` | `ctrlc::set_handler()` | TODO |
| `rt_password_read` | `rpassword::read_password()` | TODO |

### 6.2 ffi_net - Networking
**Rust libs:** `socket2`, `ureq`
**Simple packages:** web, publish, update

| FFI Function | Rust API | Status |
|--------------|----------|--------|
| `rt_http_get` | `ureq::get()` | TODO |
| `rt_http_post` | `ureq::post()` | TODO |
| `rt_http_download` | Stream to file | TODO |
| `rt_socket_create` | `socket2::Socket::new()` | TODO |
| `rt_socket_connect` | `Socket::connect()` | TODO |
| `rt_socket_bind` | `Socket::bind()` | TODO |

## Implementation Plan

### Step 1: Update FFI Generator (1 day)

1. **Modify `src/app/ffi_gen/main.spl`:**
   - Add `--gen-workspace` flag
   - Generate workspace Cargo.toml at `build/rust/Cargo.toml`
   - Generate individual crate directories

2. **Add crate spec files:**
   - `src/app/ffi_gen/specs/ffi_core.spl`
   - `src/app/ffi_gen/specs/ffi_io.spl`
   - `src/app/ffi_gen/specs/ffi_process.spl`
   - etc.

3. **Update workspace_gen.spl:**
   - Add `generate_workspace_cargo_toml()` for root
   - Add `generate_crate_cargo_toml()` for each member

### Step 2: Implement Core Crates (2 days)

1. **ffi_core:** GC, memory allocation
2. **ffi_io:** File, directory, environment (mostly done)
3. **ffi_process:** Process execution (mostly done)
4. **ffi_time:** Time operations (done)

### Step 3: Implement Build System Crates (2 days)

1. **ffi_crypto:** SHA, hash functions
2. **ffi_archive:** tar, gzip, xz
3. **ffi_system:** hostname, CPU info

### Step 4: Implement Compiler Crates (1 day)

1. **ffi_codegen:** Cranelift wrapper (mostly done)

### Step 5: Implement Data/Serde Crates (2 days)

1. **ffi_data:** regex, string interning, arena
2. **ffi_serde:** JSON, TOML, YAML, bincode

### Step 6: Implement Optional Crates (2 days)

1. **ffi_concurrent:** Threading, sync primitives
2. **ffi_cli:** REPL, file watching
3. **ffi_net:** HTTP, sockets

### Step 7: Connect to Simple Packages (1 day)

1. **Update `src/app/io/mod.spl`:**
   - Add new extern fn declarations
   - Add wrapper functions

2. **Update Simple packages to use new wrappers**

## Simple Package → FFI Crate Mapping

| Simple Package | FFI Crates Required |
|----------------|---------------------|
| **build** | ffi_core, ffi_io, ffi_process, ffi_time, ffi_crypto, ffi_system |
| **test_runner_new** | ffi_core, ffi_io, ffi_process, ffi_time, ffi_system |
| **cli** | ffi_core, ffi_io, ffi_process, ffi_codegen, ffi_cli |
| **formatter** | ffi_core, ffi_io, ffi_data |
| **lint** | ffi_core, ffi_io, ffi_data |
| **package** | ffi_core, ffi_io, ffi_archive, ffi_crypto |
| **compile** | ffi_core, ffi_io, ffi_codegen |
| **repl** | ffi_core, ffi_io, ffi_cli |
| **watch** | ffi_core, ffi_io, ffi_cli |
| **publish** | ffi_core, ffi_io, ffi_net, ffi_crypto |
| **lms** | ffi_core, ffi_io, ffi_torch |
| **deeplearning** | ffi_core, ffi_torch, ffi_cuda (optional) |
| **gpu** | ffi_core, ffi_vulkan or ffi_cuda |
| **graphics** | ffi_core, ffi_vulkan |

## Generated File Summary

```
Total files to generate:
├── build/rust/Cargo.toml                 (workspace root)
├── build/rust/rust-toolchain.toml        (toolchain config)
├── 16 crate directories
│   ├── 16 Cargo.toml files
│   └── ~60 .rs source files
└── src/app/io/mod.spl                    (Simple FFI declarations)

Estimated lines of code:
├── Rust FFI wrappers: ~8,000 LOC (including GPU/ML)
├── Simple declarations: ~800 LOC
└── Generator updates: ~500 LOC

Crate breakdown:
├── Core (4 crates): ffi_core, ffi_io, ffi_process, ffi_time
├── Build (3 crates): ffi_crypto, ffi_archive, ffi_system
├── Compiler (1 crate): ffi_codegen
├── Data (2 crates): ffi_data, ffi_serde
├── Concurrency (1 crate): ffi_concurrent
├── CLI/Net (2 crates): ffi_cli, ffi_net
└── GPU/ML (3 crates): ffi_torch, ffi_cuda, ffi_vulkan [OPTIONAL]
```

## Success Criteria

1. All 13 FFI crates compile with `cargo check`
2. All existing Simple tests pass
3. `simple build` works using new FFI wrappers
4. `simple test` works using new FFI wrappers
5. Binary size within 10% of current bootstrap (9.3 MB)

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| Phase 1 | 3 days | Core crates (ffi_core, ffi_io, ffi_process, ffi_time) |
| Phase 2 | 2 days | Build system crates (ffi_crypto, ffi_archive, ffi_system) |
| Phase 3 | 1 day | Compiler crate (ffi_codegen) |
| Phase 4 | 2 days | Data/serde crates |
| Phase 5 | 2 days | Concurrency crates |
| Phase 6 | 3 days | GPU/ML crates (ffi_torch, ffi_cuda, ffi_vulkan) - **Optional** |
| Phase 7 | 2 days | CLI/Net crates (ffi_cli, ffi_net) |
| Phase 8 | 1 day | Integration & testing |
| **Total** | **16 days** | Complete FFI wrapper system (13 days without GPU/ML) |

## Next Steps

1. [ ] Update FFI generator for multi-crate workspace
2. [ ] Create spec files for each crate
3. [ ] Generate Phase 1 crates
4. [ ] Test with `simple build`
5. [ ] Continue with remaining phases
