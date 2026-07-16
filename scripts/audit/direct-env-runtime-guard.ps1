$ErrorActionPreference = "Stop"
$Mode = if ($args.Count -gt 0) { [string]$args[0] } else { "--all" }
if (@("--all", "--working", "--staged", "--self-test", "-h", "--help") -notcontains $Mode) {
    Write-Error "unknown mode: $Mode"
    exit 2
}
$RootDir = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..\..")).Path
Set-Location -LiteralPath $RootDir

$ForbiddenPattern = 'extern fn rt_env_(get|cwd)\s*\(|rt_env_(get|cwd)\s*\(|extern fn rt_process_(run(_timeout)?|spawn_async|wait|is_running|is_alive|kill)\s*\(|rt_process_(run(_timeout)?|spawn_async|wait|is_running|is_alive|kill)\s*\(|^(use|import|from|export\s+use)\s.*rt_env_(get|cwd)([^A-Za-z0-9_]|$)|^(use|import|from|export\s+use)\s.*rt_process_(run(_timeout)?|spawn_async|wait|is_running|is_alive|kill)([^A-Za-z0-9_]|$)'

function Show-Usage {
    @"
Usage: powershell -ExecutionPolicy Bypass -File scripts\audit\direct-env-runtime-guard.ps1 [--all|--working|--staged|--self-test]

Blocks direct rt_env_get/cwd and direct process run/spawn/lifecycle calls or
imports in production app leaf code and gc_async_mut lib code outside runtime
owner modules. Use app/std/gc env and process facades instead.
"@
}

function Test-AllowedOwner([string]$Path) {
    $normalized = $Path.Replace("\", "/")
    return $normalized.StartsWith("src/app/io/") -or
        $normalized.StartsWith("src/app/ffi_gen.specs/") -or
        $normalized -eq "src/lib/nogc_sync_mut/io/env_ops.spl"
}

function Get-GuardPaths {
    if ($Mode -eq "--all") {
        if ((Get-Command jj -ErrorAction SilentlyContinue) -and (Test-Path -LiteralPath ".jj")) {
            jj file list src/app src/lib/gc_async_mut | Where-Object { $_ -like "*.spl" }
        } elseif (Test-Path -LiteralPath ".git") {
            git ls-files src/app src/lib/gc_async_mut | Where-Object { $_ -like "*.spl" }
        }
    } elseif ($Mode -eq "--working") {
        if ((Get-Command jj -ErrorAction SilentlyContinue) -and (Test-Path -LiteralPath ".jj")) {
            jj diff --name-only -- src/app src/lib/gc_async_mut | Where-Object { $_ -like "*.spl" }
        } elseif (Test-Path -LiteralPath ".git") {
            $changed = git diff --name-only -- src/app src/lib/gc_async_mut
            $untracked = git ls-files --others --exclude-standard -- src/app src/lib/gc_async_mut
            @($changed) + @($untracked) | Where-Object { $_ -like "*.spl" }
        }
    } elseif ($Mode -eq "--staged") {
        if (Test-Path -LiteralPath ".git") {
            git diff --cached --name-only -- src/app src/lib/gc_async_mut | Where-Object { $_ -like "*.spl" }
        }
    }
}

function Invoke-SelfTest {
    $tmpDir = Join-Path ([IO.Path]::GetTempPath()) ("direct-env-runtime-guard-" + [Guid]::NewGuid().ToString("N"))
    New-Item -ItemType Directory -Force -Path $tmpDir | Out-Null
    try {
        $rawImport = Join-Path $tmpDir "raw_import.spl"
        $facadeImport = Join-Path $tmpDir "facade_import.spl"
        $rawCall = Join-Path $tmpDir "raw_call.spl"
        $envHandleOwner = Join-Path $tmpDir "env_handle_owner.spl"
        Set-Content -LiteralPath $rawImport -Value 'use std.env.types.{rt_process_run}'
        Set-Content -LiteralPath $facadeImport -Value 'use app.io.mod.{process_run_timeout}'
        Set-Content -LiteralPath $rawCall -Value 'val result = rt_process_spawn_async("sh", ["-c", "true"])'
        Set-Content -LiteralPath $envHandleOwner -Value 'extern fn rt_env_get_var(env_handle: i64, name: text) -> auto'

        if (-not (Select-String -LiteralPath $rawImport -Pattern $ForbiddenPattern -Quiet)) {
            Write-Error "STATUS: FAIL direct-env-runtime-guard self-test raw import not detected"
        }
        if (-not (Select-String -LiteralPath $rawCall -Pattern $ForbiddenPattern -Quiet)) {
            Write-Error "STATUS: FAIL direct-env-runtime-guard self-test raw call not detected"
        }
        if (Select-String -LiteralPath $facadeImport -Pattern $ForbiddenPattern -Quiet) {
            Write-Error "STATUS: FAIL direct-env-runtime-guard self-test facade import rejected"
        }
        if (Select-String -LiteralPath $envHandleOwner -Pattern $ForbiddenPattern -Quiet) {
            Write-Error "STATUS: FAIL direct-env-runtime-guard self-test env handle owner rejected"
        }
        Write-Output "STATUS: PASS direct-env-runtime-guard self-test"
    } finally {
        Remove-Item -LiteralPath $tmpDir -Recurse -Force -ErrorAction SilentlyContinue
    }
}

if ($Mode -eq "-h" -or $Mode -eq "--help") {
    Show-Usage
    exit 0
}

if ($Mode -eq "--self-test") {
    Invoke-SelfTest
    exit 0
}

$failures = New-Object System.Collections.Generic.List[string]
$paths = @(Get-GuardPaths | Sort-Object -Unique)
foreach ($path in $paths) {
    if (-not (Test-Path -LiteralPath $path)) { continue }
    if (Test-AllowedOwner $path) { continue }
    Select-String -LiteralPath $path -Pattern $ForbiddenPattern | ForEach-Object {
        $failures.Add("$path`:$($_.LineNumber):$($_.Line)")
    }
}

if ($failures.Count -gt 0) {
    $failures | ForEach-Object { Write-Error $_ }
    Write-Error "STATUS: FAIL direct env/process runtime call outside owners"
    exit 1
}

Write-Output "STATUS: PASS direct-env-runtime-guard"
