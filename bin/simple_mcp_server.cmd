@echo off
setlocal
set "EXE=%~dp0release\x86_64-pc-windows-msvc\simple_mcp_server.exe"
if not "%SIMPLE_MCP_NATIVE%"=="" set "EXE=%SIMPLE_MCP_NATIVE%"
if exist "%EXE%" (
    "%EXE%" %*
    exit /b %ERRORLEVEL%
)
if not "%SIMPLE_MCP_NATIVE%"=="" (
    echo error: SIMPLE_MCP_NATIVE not found: %SIMPLE_MCP_NATIVE% 1>&2
    exit /b 127
)
set "NATIVE_CMD=%~dp0release\x86_64-pc-windows-msvc\simple_mcp_server.cmd"
if exist "%NATIVE_CMD%" (
    call "%NATIVE_CMD%" %*
    exit /b %ERRORLEVEL%
)
if "%SIMPLE_MCP_ALLOW_SOURCE_FALLBACK%"=="1" goto :source
echo error: cached native simple_mcp_server not found 1>&2
echo source fallback disabled; set SIMPLE_MCP_ALLOW_SOURCE_FALLBACK=1 only for debugging 1>&2
exit /b 127

:source
if "%SIMPLE_LIB%"=="" set "SIMPLE_LIB=%~dp0..\src"
if "%SIMPLE_LOG%"=="" set "SIMPLE_LOG=error"
if "%RUST_LOG%"=="" set "RUST_LOG=error"
set "SIMPLE_RUNTIME=%~dp0release\x86_64-pc-windows-msvc\simple.exe"
if not "%SIMPLE_BINARY%"=="" set "SIMPLE_RUNTIME=%SIMPLE_BINARY%"
if not exist "%SIMPLE_RUNTIME%" (
    echo error: deployed pure-Simple runtime not found for source debugging 1>&2
    exit /b 127
)
"%SIMPLE_RUNTIME%" run "%~dp0..\src\app\mcp\main.spl" %*
exit /b %ERRORLEVEL%
