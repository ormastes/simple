@echo off
setlocal
set "SCRIPT_DIR=%~dp0"
set "RUNTIME=%SCRIPT_DIR%release\simple.exe"
if not exist "%RUNTIME%" set "RUNTIME=%SCRIPT_DIR%release\simple"
set "ENTRY=%SCRIPT_DIR%..\examples\10_tooling\trace32_tools\t32_lsp_mcp\main.spl"
set "REPO_ROOT=%SCRIPT_DIR%.."
set "TRACE32_ROOT=%REPO_ROOT%\examples\10_tooling\trace32_tools"
pushd "%REPO_ROOT%"
set "SIMPLE_LIB=%TRACE32_ROOT%"
set "SIMPLE_RUNTIME=%RUNTIME%"
set "T32_LSP_MCP_TOOL_RUNNER=examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl"
set "SIMPLE_LOG=error"
set "RUST_LOG=error"
"%RUNTIME%" "%ENTRY%" %* 2>nul
