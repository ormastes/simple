@echo off
setlocal
set "SCRIPT_DIR=%~dp0"
set "RUNTIME=%SCRIPT_DIR%simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%simple"
set "REPO_ROOT=%SCRIPT_DIR%.."
set "TRACE32_ROOT=%REPO_ROOT%\examples\10_tooling\trace32_tools"
set "ENTRY=%TRACE32_ROOT%\t32_lsp_mcp\claude_frontend.spl"
pushd "%REPO_ROOT%"

rem SIMPLE_LIB points to trace32_tools — claude_frontend.spl is standalone (no imports)
set "SIMPLE_LIB=%TRACE32_ROOT%"
set "SIMPLE_RUNTIME=%RUNTIME%"
set "SIMPLE_BINARY=%RUNTIME%"
set "SIMPLE_TIMEOUT_SECONDS=86400"
set "SIMPLE_MEMORY_LIMIT_MB=512"
set "T32_LSP_MCP_TOOL_RUNNER=examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl"
rem Only set TOOL_RUNNER_BIN if the compiled binary exists (matches node launcher isExecutable guard)
if exist "%REPO_ROOT%\bin\release\t32_lsp_mcp_tool_runner.exe" set "T32_LSP_MCP_TOOL_RUNNER_BIN=%REPO_ROOT%\bin\release\t32_lsp_mcp_tool_runner.exe"
if exist "%REPO_ROOT%\bin\release\t32_lsp_mcp_tool_runner" set "T32_LSP_MCP_TOOL_RUNNER_BIN=%REPO_ROOT%\bin\release\t32_lsp_mcp_tool_runner"
set "T32_LSP_MCP_TOOL_DAEMON=examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl"
set "T32_LSP_MCP_TOOL_DAEMON_DIR=%TEMP%\t32_lsp_mcp_shared"
set "SIMPLE_LOG=error"
set "RUST_LOG=error"
"%RUNTIME%" "%ENTRY%" %* 2>nul
