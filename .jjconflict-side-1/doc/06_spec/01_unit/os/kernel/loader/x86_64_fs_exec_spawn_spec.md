# x86_64 Filesystem Executable Launch

Source: `test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl`

Status: source contract implemented; live QEMU proof pending. Stubs: 0.

## Flow

```text
requested VFS path → bounded ELF header/program headers
                   → stream each PT_LOAD into mapped user frames
                   → build argc/argv/envp/auxv → enter ring 3
```

## Scenario: stream the requested filesystem ELF

1. Open the exact requested path with `simpleos_fat32_stream_open(path)`.
2. Retain at most the bounded ELF/program-header prefix.
3. Stream every PT_LOAD range directly to its physical destination.
4. Fail on a short range read or wrapped/out-of-file ELF range.
5. Never substitute the unkeyed boot-preload buffer.

Legacy SMF/extracted-image callers remain blob-backed and copy from the supplied
ELF blob; they do not reuse raw container-file offsets.

## Scenario: preserve the shell dispatch path

Shell PATH execution continues through `fs_exec_spawn_ring3` and the existing
architecture dispatcher. No seeded-app registry or parallel loader is added.

## Scenario: construct process arguments

The loader places the binary path at `argv[0]`, appends caller argv, then writes
envp and the `AT_PAGESZ`, `AT_EXECFN`, and `AT_NULL` auxiliary entries. The
single-page startup frame is bounded to 64 caller arguments, 64 environment
entries, and 4096 bytes; overflow fails before ring-3 entry.

## Verification

The focused source spec checks both stream and blob sources, the short-read
failure, preload absence, shell dispatch, and real SysV argument population.
Final acceptance additionally requires the QEMU Clang and Simple filesystem
launch scenarios.
