# Windows hardening MCP step - 2026-05-30

## Scope

MCP reinstall and Windows bootstrap checks for `simple-mcp` and
`simple-lsp-mcp`.

## Changes

- Added `config/mcp/install.ps1` so Windows users can reinstall project and
  Codex MCP configuration without requiring `sh` or `/bin/sh`.
- Updated `doc/07_guide/tooling/mcp.md` with the native Windows install command.
- Fixed Windows Rust bootstrap build blockers found while validating MCP:
  - corrected `std::os::windows::ffi::OsStrExt` imports,
  - gated Unix-only socket/watchdog/async-driver paths,
  - added Windows Unix-domain socket stubs,
  - switched runtime C build integration to `cc::Build`,
  - added Windows wall-clock/monotonic time support in `runtime_time.c`,
  - added Windows dynamic loading for CUDA, Vulkan, and shaderc interpreter
    extern fallbacks.

## Evidence

- `powershell -ExecutionPolicy Bypass -File config\mcp\install.ps1` succeeded:
  installed Windows `.mcp.json`, registered `simple-mcp`, `simple-lsp-mcp`,
  and `stitch-mcp` in Codex.
- `codex mcp list` showed `simple-mcp` and `simple-lsp-mcp` enabled with
  absolute `.cmd` launchers.
- `cargo build --manifest-path src\compiler_rust\Cargo.toml -p simple-driver --bin simple`
  passed on Windows.
- `src\compiler_rust\target\debug\simple.exe check src\app\mcp` passed
  26 files.
- `src\compiler_rust\target\debug\simple.exe check src\app\simple_lsp_mcp`
  passed 5 files.

## Remaining MCP Windows blocker

Native MCP packaging still fails after the driver build succeeds. The focused
command:

```powershell
src\compiler_rust\target\debug\simple.exe native-build --runtime-bundle core-c --source src\compiler --source src\app --source src\lib --entry-closure --entry src\app\mcp\main.spl --output build\windows-hardening\simple_mcp_server.exe
```

fails in the Windows native-build linker path. Current evidence points to the
MinGW lane generating duplicate stubs for symbols already provided by Windows
system libraries and failing to find `-lvcruntime`. This is separate from MCP
reinstall and Rust bootstrap compilation, and should be handled in the next
Windows native-build hardening slice.
