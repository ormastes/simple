param(
    [string]$EvidencePath = "build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env",
    [string]$QemuBinary = $env:QEMU_SYSTEM_RISCV64,
    [string]$KernelPath = "build/os/simpleos_riscv64_smf_fs.elf",
    [string]$ImagePath = "build/os/fat32-riscv64.img",
    [int]$SshPort = 2222,
    [int]$HttpPort = 8080,
    [int]$ProbeTimeoutMs = 1000,
    [switch]$RunLiveBoot,
    [int]$BootTimeoutSeconds = 60,
    [string]$ArtifactDir = "build/os/systest/qemu-riscv64-desktop",
    [string]$SerialLogPath = "",
    [int]$QmpPort = 4444,
    [string]$ScreendumpPath = "",
    [switch]$AttemptBuild,
    [string]$BuildSimpleBinary = "src\compiler_rust\target\debug\simple.exe",
    [string]$NestedSimpleBinary = "",
    [string]$BuildLogPath = "",
    [string]$BuildBackend = $env:SIMPLE_OS_BUILD_BACKEND,
    [string]$BuildCc = $env:CC,
    [switch]$BuildDesktopServiceKernel,
    [string]$DesktopServiceKernelPath = "build/os/simpleos_riscv64_desktop_service.elf",
    [string]$DesktopServiceEntry = "examples/09_embedded/simple_os/arch/riscv64/desktop_service_entry.spl",
    [string]$DesktopServiceBuildLogPath = "",
    [switch]$BuildDiskImage,
    [string]$DiskImageBuilderCompiler = "",
    [string]$DiskImageBuilderPath = "build\tools\make_os_disk.exe",
    [string]$DiskImageBuilderSource = "scripts\os\make_os_disk.c",
    [switch]$KeepQemu
)

$ErrorActionPreference = "Stop"

function Write-Row($rows, [string]$key, [string]$value) {
    $rows.Add("$key=$value") | Out-Null
}

function Test-TcpPort([string]$hostName, [int]$port, [int]$timeoutMs) {
    $client = [System.Net.Sockets.TcpClient]::new()
    try {
        $async = $client.BeginConnect($hostName, $port, $null, $null)
        if (-not $async.AsyncWaitHandle.WaitOne($timeoutMs)) {
            return $false
        }
        $client.EndConnect($async)
        return $true
    } catch {
        return $false
    } finally {
        $client.Close()
    }
}

function Read-TextFileOrEmpty([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return ""
    }
    $resolved = (Resolve-Path -LiteralPath $path).Path
    for ($attempt = 0; $attempt -lt 5; $attempt++) {
        $stream = $null
        $reader = $null
        try {
            $stream = [System.IO.FileStream]::new(
                $resolved,
                [System.IO.FileMode]::Open,
                [System.IO.FileAccess]::Read,
                [System.IO.FileShare]::ReadWrite -bor [System.IO.FileShare]::Delete
            )
            $reader = [System.IO.StreamReader]::new($stream, [System.Text.Encoding]::UTF8, $true)
            return $reader.ReadToEnd()
        } catch {
            Start-Sleep -Milliseconds 50
        } finally {
            if ($reader) {
                $reader.Dispose()
            } elseif ($stream) {
                $stream.Dispose()
            }
        }
    }
    return ""
}

function Test-TextContains([string]$text, [string]$needle) {
    if ([string]::IsNullOrEmpty($text)) {
        return $false
    }
    return $text.Contains($needle)
}

function Read-SshBanner([int]$port, [int]$timeoutMs) {
    $client = [System.Net.Sockets.TcpClient]::new()
    try {
        $async = $client.BeginConnect("127.0.0.1", $port, $null, $null)
        if (-not $async.AsyncWaitHandle.WaitOne($timeoutMs)) {
            return ""
        }
        $client.EndConnect($async)
        $stream = $client.GetStream()
        $stream.ReadTimeout = $timeoutMs
        $buffer = New-Object byte[] 256
        $count = $stream.Read($buffer, 0, $buffer.Length)
        if ($count -le 0) {
            return ""
        }
        return [System.Text.Encoding]::ASCII.GetString($buffer, 0, $count).Trim()
    } catch {
        return ""
    } finally {
        $client.Close()
    }
}

function Invoke-HttpStatusCode([int]$port, [int]$timeoutMs) {
    $client = [System.Net.Sockets.TcpClient]::new()
    try {
        $async = $client.BeginConnect("127.0.0.1", $port, $null, $null)
        if (-not $async.AsyncWaitHandle.WaitOne($timeoutMs)) {
            return 0
        }
        $client.EndConnect($async)
        $stream = $client.GetStream()
        $stream.ReadTimeout = $timeoutMs
        $request = "GET / HTTP/1.0`r`nHost: 127.0.0.1`r`nConnection: close`r`n`r`n"
        $bytes = [System.Text.Encoding]::ASCII.GetBytes($request)
        $stream.Write($bytes, 0, $bytes.Length)
        $buffer = New-Object byte[] 512
        $count = $stream.Read($buffer, 0, $buffer.Length)
        if ($count -le 0) {
            return 0
        }
        $response = [System.Text.Encoding]::ASCII.GetString($buffer, 0, $count)
        if ($response -match '^HTTP/\d\.\d\s+(\d+)') {
            return [int]$Matches[1]
        }
        return 0
    } catch {
        return 0
    } finally {
        $client.Close()
    }
}

function Invoke-QmpCommand([int]$port, [string]$json, [int]$timeoutMs) {
    $client = [System.Net.Sockets.TcpClient]::new()
    try {
        $async = $client.BeginConnect("127.0.0.1", $port, $null, $null)
        if (-not $async.AsyncWaitHandle.WaitOne($timeoutMs)) {
            return ""
        }
        $client.EndConnect($async)
        $stream = $client.GetStream()
        $stream.ReadTimeout = $timeoutMs
        $stream.WriteTimeout = $timeoutMs
        $buffer = New-Object byte[] 4096
        try {
            $null = $stream.Read($buffer, 0, $buffer.Length)
        } catch {
        }
        $payload = [System.Text.Encoding]::ASCII.GetBytes($json + "`r`n")
        $stream.Write($payload, 0, $payload.Length)
        $count = $stream.Read($buffer, 0, $buffer.Length)
        if ($count -le 0) {
            return ""
        }
        return [System.Text.Encoding]::ASCII.GetString($buffer, 0, $count)
    } catch {
        return ""
    } finally {
        $client.Close()
    }
}

function Invoke-QmpScreendump([int]$port, [string]$path, [int]$timeoutMs) {
    $client = [System.Net.Sockets.TcpClient]::new()
    try {
        $async = $client.BeginConnect("127.0.0.1", $port, $null, $null)
        if (-not $async.AsyncWaitHandle.WaitOne($timeoutMs)) {
            return "blocked:qmp-connect-failed"
        }
        $client.EndConnect($async)
        $stream = $client.GetStream()
        $stream.ReadTimeout = $timeoutMs
        $stream.WriteTimeout = $timeoutMs
        $buffer = New-Object byte[] 4096
        try {
            $null = $stream.Read($buffer, 0, $buffer.Length)
        } catch {
        }
        $capPayload = [System.Text.Encoding]::ASCII.GetBytes('{"execute":"qmp_capabilities"}' + "`r`n")
        $stream.Write($capPayload, 0, $capPayload.Length)
        $capCount = $stream.Read($buffer, 0, $buffer.Length)
        if ($capCount -le 0) {
            return "blocked:qmp-capabilities-failed"
        }
        $escapedPath = $path.Replace("\", "\\")
        $command = '{"execute":"screendump","arguments":{"filename":"' + $escapedPath + '"}}'
        $payload = [System.Text.Encoding]::ASCII.GetBytes($command + "`r`n")
        $stream.Write($payload, 0, $payload.Length)
        $count = $stream.Read($buffer, 0, $buffer.Length)
        if ($count -le 0) {
            return "blocked:qmp-screendump-failed"
        }
        $deadline = (Get-Date).AddSeconds(5)
        while ((Get-Date) -lt $deadline) {
            if (Test-Path -LiteralPath $path) {
                return "pass"
            }
            Start-Sleep -Milliseconds 100
        }
        return "blocked:qmp-screendump-missing-file"
    } catch {
        return "blocked:qmp-screendump-error"
    } finally {
        $client.Close()
    }
}

function Test-PpmNonblank([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return "missing"
    }
    $bytes = [System.IO.File]::ReadAllBytes((Resolve-Path -LiteralPath $path))
    if ($bytes.Length -le 32) {
        return "blocked:ppm-too-small"
    }
    if ($bytes[0] -ne [byte][char]'P' -or $bytes[1] -ne [byte][char]'6') {
        return "blocked:not-p6-ppm"
    }
    $first = $bytes[$bytes.Length - 1]
    $different = $false
    $start = [Math]::Max(0, $bytes.Length - 4096)
    for ($i = $start; $i -lt $bytes.Length; $i++) {
        if ($bytes[$i] -ne $first) {
            $different = $true
            break
        }
    }
    if ($different) {
        return "pass"
    }
    return "blocked:blank-ppm"
}

function Join-Values([string[]]$values) {
    ($values | Where-Object { -not [string]::IsNullOrWhiteSpace($_) }) -join ";"
}

function First-ExistingPath([string[]]$paths) {
    foreach ($path in $paths) {
        if ((-not [string]::IsNullOrWhiteSpace($path)) -and (Test-Path -LiteralPath $path)) {
            return $path
        }
    }
    return ""
}

$scriptDir = Split-Path -Parent $PSCommandPath
$repoRoot = Resolve-Path -LiteralPath (Join-Path $scriptDir "..\..")
Set-Location $repoRoot

function Resolve-RepoPath([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path)) {
        return $path
    }
    if ([System.IO.Path]::IsPathRooted($path)) {
        return $path
    }
    return Join-Path $repoRoot $path
}

$EvidencePath = Resolve-RepoPath $EvidencePath
$KernelPath = Resolve-RepoPath $KernelPath
$ImagePath = Resolve-RepoPath $ImagePath
$ArtifactDir = Resolve-RepoPath $ArtifactDir
$SerialLogPath = Resolve-RepoPath $SerialLogPath
$ScreendumpPath = Resolve-RepoPath $ScreendumpPath
$BuildSimpleBinary = Resolve-RepoPath $BuildSimpleBinary
$NestedSimpleBinary = Resolve-RepoPath $NestedSimpleBinary
$BuildLogPath = Resolve-RepoPath $BuildLogPath
$DesktopServiceKernelPath = Resolve-RepoPath $DesktopServiceKernelPath
$DesktopServiceEntry = Resolve-RepoPath $DesktopServiceEntry
$DesktopServiceBuildLogPath = Resolve-RepoPath $DesktopServiceBuildLogPath
$DiskImageBuilderPath = Resolve-RepoPath $DiskImageBuilderPath
$DiskImageBuilderSource = Resolve-RepoPath $DiskImageBuilderSource

if ([string]::IsNullOrWhiteSpace($QemuBinary)) {
    $cmd = Get-Command qemu-system-riscv64 -ErrorAction SilentlyContinue
    if ($cmd) {
        $QemuBinary = $cmd.Source
    }
}

$rows = [System.Collections.Generic.List[string]]::new()
$evidenceDir = Split-Path -Parent $EvidencePath
if (-not [string]::IsNullOrWhiteSpace($evidenceDir)) {
    New-Item -ItemType Directory -Force -Path $evidenceDir | Out-Null
}
if ([string]::IsNullOrWhiteSpace($SerialLogPath)) {
    $SerialLogPath = Join-Path $ArtifactDir "serial.log"
}
if ([string]::IsNullOrWhiteSpace($ScreendumpPath)) {
    $ScreendumpPath = Join-Path $ArtifactDir "qemu-screendump.ppm"
}
New-Item -ItemType Directory -Force -Path $ArtifactDir | Out-Null
$qemuStdoutPath = Join-Path $ArtifactDir "qemu.stdout.log"
$qemuStderrPath = Join-Path $ArtifactDir "qemu.stderr.log"

$qemuPresent = -not [string]::IsNullOrWhiteSpace($QemuBinary) -and (Test-Path -LiteralPath $QemuBinary)

$canonicalKernelPath = Resolve-RepoPath "build/os/simpleos_riscv64_smf_fs.elf"
$legacyKernelPath = Resolve-RepoPath "build/os/simpleos_riscv64.elf"
$fpgaKernelPath = Resolve-RepoPath "build/os/simpleos_riscv64_fpga.elf"
$canonicalImagePath = Resolve-RepoPath "build/os/fat32-riscv64.img"
$storageProbeImagePath = Resolve-RepoPath "build/qemu-rv64-storage-probe.img"
if ([string]::IsNullOrWhiteSpace($BuildLogPath)) {
    $BuildLogPath = Join-Path $ArtifactDir "rv64-build.log"
}
$buildAttempted = $false
$buildStatus = "not-requested"
$buildExitCode = ""
$buildNativeExitCode = ""
$buildCommand = "$BuildSimpleBinary os build --arch=riscv64"
$buildError = ""
$nestedSimpleBinaryUsed = ""
$nestedSimpleBinarySource = "not-requested"
$buildCcUsed = ""
$buildCcSource = "not-requested"
$desktopServiceBuildAttempted = $false
$desktopServiceBuildStatus = "not-requested"
$desktopServiceBuildExitCode = ""
$desktopServiceBuildCommand = "$BuildSimpleBinary native-build --source build/os/generated --source examples/09_embedded/simple_os/arch/riscv64 --backend cranelift --opt-level=aggressive --log on --timeout 180 --entry-closure --entry $DesktopServiceEntry --target riscv64-unknown-none -o $DesktopServiceKernelPath --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld"
if ([string]::IsNullOrWhiteSpace($DesktopServiceBuildLogPath)) {
    $DesktopServiceBuildLogPath = Join-Path $ArtifactDir "rv64-desktop-service-build.log"
}

if ($AttemptBuild) {
    $buildAttempted = $true
    Remove-Item -LiteralPath $BuildLogPath -Force -ErrorAction SilentlyContinue
    if ([string]::IsNullOrWhiteSpace($BuildSimpleBinary) -or -not (Test-Path -LiteralPath $BuildSimpleBinary)) {
        $buildStatus = "blocked:missing-simple-build-binary"
    } else {
        $oldBackend = $env:SIMPLE_OS_BUILD_BACKEND
        $oldSimpleBinary = $env:SIMPLE_BINARY
        $oldCc = $env:CC
        try {
            if (-not [string]::IsNullOrWhiteSpace($BuildBackend)) {
                $env:SIMPLE_OS_BUILD_BACKEND = $BuildBackend
            }
            if (-not [string]::IsNullOrWhiteSpace($NestedSimpleBinary)) {
                $env:SIMPLE_BINARY = $NestedSimpleBinary
                $nestedSimpleBinaryUsed = $NestedSimpleBinary
                $nestedSimpleBinarySource = "param"
            } elseif ([string]::IsNullOrWhiteSpace($env:SIMPLE_BINARY)) {
                $env:SIMPLE_BINARY = $BuildSimpleBinary
                $nestedSimpleBinaryUsed = $BuildSimpleBinary
                $nestedSimpleBinarySource = "build-simple-binary"
            } else {
                $nestedSimpleBinaryUsed = $env:SIMPLE_BINARY
                $nestedSimpleBinarySource = "environment"
            }
            if (-not [string]::IsNullOrWhiteSpace($BuildCc)) {
                $env:CC = $BuildCc
                $buildCcUsed = $BuildCc
                $buildCcSource = "param-or-environment"
            } elseif (-not [string]::IsNullOrWhiteSpace($env:CC)) {
                $buildCcUsed = $env:CC
                $buildCcSource = "environment"
            }
            $buildStdoutPath = "$BuildLogPath.stdout"
            $buildStderrPath = "$BuildLogPath.stderr"
            Remove-Item -LiteralPath $buildStdoutPath -Force -ErrorAction SilentlyContinue
            Remove-Item -LiteralPath $buildStderrPath -Force -ErrorAction SilentlyContinue
            $process = Start-Process -FilePath $BuildSimpleBinary -ArgumentList @("os", "build", "--arch=riscv64") -RedirectStandardOutput $buildStdoutPath -RedirectStandardError $buildStderrPath -NoNewWindow -Wait -PassThru
            $stdout = if (Test-Path -LiteralPath $buildStdoutPath) { Get-Content -Raw -LiteralPath $buildStdoutPath } else { "" }
            $stderr = if (Test-Path -LiteralPath $buildStderrPath) { Get-Content -Raw -LiteralPath $buildStderrPath } else { "" }
            $buildLogText = ($stdout + "`r`n" + $stderr)
            $buildLogText | Set-Content -Encoding ASCII -Path $BuildLogPath
            Remove-Item -LiteralPath $buildStdoutPath -Force -ErrorAction SilentlyContinue
            Remove-Item -LiteralPath $buildStderrPath -Force -ErrorAction SilentlyContinue
            $buildExitCode = "$($process.ExitCode)"
            if ($buildLogText -match 'phase=native-build FAILED exit=([^\s]+)') {
                $buildNativeExitCode = $Matches[1]
            }
            if ($process.ExitCode -eq 0) {
                $buildStatus = "pass"
            } else {
                $buildStatus = "blocked:build-exit-$($process.ExitCode)"
            }
            if ($null -eq $oldBackend) {
                Remove-Item Env:SIMPLE_OS_BUILD_BACKEND -ErrorAction SilentlyContinue
            } else {
                $env:SIMPLE_OS_BUILD_BACKEND = $oldBackend
            }
            if ($null -eq $oldSimpleBinary) {
                Remove-Item Env:SIMPLE_BINARY -ErrorAction SilentlyContinue
            } else {
                $env:SIMPLE_BINARY = $oldSimpleBinary
            }
            if ($null -eq $oldCc) {
                Remove-Item Env:CC -ErrorAction SilentlyContinue
            } else {
                $env:CC = $oldCc
            }
        } catch {
            $buildStatus = "blocked:build-launch-failed"
            $buildError = $_.Exception.Message
            if ($null -eq $oldBackend) {
                Remove-Item Env:SIMPLE_OS_BUILD_BACKEND -ErrorAction SilentlyContinue
            } else {
                $env:SIMPLE_OS_BUILD_BACKEND = $oldBackend
            }
            if ($null -eq $oldSimpleBinary) {
                Remove-Item Env:SIMPLE_BINARY -ErrorAction SilentlyContinue
            } else {
                $env:SIMPLE_BINARY = $oldSimpleBinary
            }
            if ($null -eq $oldCc) {
                Remove-Item Env:CC -ErrorAction SilentlyContinue
            } else {
                $env:CC = $oldCc
            }
        }
    }
}

if ($BuildDesktopServiceKernel) {
    $desktopServiceBuildAttempted = $true
    Remove-Item -LiteralPath $DesktopServiceBuildLogPath -Force -ErrorAction SilentlyContinue
    if ([string]::IsNullOrWhiteSpace($BuildSimpleBinary) -or -not (Test-Path -LiteralPath $BuildSimpleBinary)) {
        $desktopServiceBuildStatus = "blocked:missing-simple-build-binary"
    } elseif ([string]::IsNullOrWhiteSpace($BuildCc) -or -not (Test-Path -LiteralPath $BuildCc)) {
        $desktopServiceBuildStatus = "blocked:missing-build-cc"
    } elseif (-not (Test-Path -LiteralPath $DesktopServiceEntry)) {
        $desktopServiceBuildStatus = "blocked:missing-desktop-service-entry"
    } else {
        $oldBackend = $env:SIMPLE_OS_BUILD_BACKEND
        $oldSimpleLib = $env:SIMPLE_LIB
        $oldCc = $env:CC
        try {
            $env:SIMPLE_OS_BUILD_BACKEND = $(if ([string]::IsNullOrWhiteSpace($BuildBackend)) { "cranelift" } else { $BuildBackend })
            $env:SIMPLE_LIB = "src"
            $env:CC = $BuildCc
            $desktopStdoutPath = "$DesktopServiceBuildLogPath.stdout"
            $desktopStderrPath = "$DesktopServiceBuildLogPath.stderr"
            Remove-Item -LiteralPath $desktopStdoutPath, $desktopStderrPath -Force -ErrorAction SilentlyContinue
            $desktopArgs = @(
                "native-build",
                "--source", "build/os/generated",
                "--source", "examples/09_embedded/simple_os/arch/riscv64",
                "--backend", $(if ([string]::IsNullOrWhiteSpace($BuildBackend)) { "cranelift" } else { $BuildBackend }),
                "--opt-level=aggressive",
                "--log", "on",
                "--timeout", "180",
                "--entry-closure",
                "--entry", $DesktopServiceEntry,
                "--target", "riscv64-unknown-none",
                "-o", $DesktopServiceKernelPath,
                "--linker-script", "examples/09_embedded/simple_os/arch/riscv64/linker.ld"
            )
            $desktopProcess = Start-Process -FilePath $BuildSimpleBinary -ArgumentList $desktopArgs -RedirectStandardOutput $desktopStdoutPath -RedirectStandardError $desktopStderrPath -NoNewWindow -Wait -PassThru
            $desktopServiceBuildExitCode = "$($desktopProcess.ExitCode)"
            $desktopStdout = if (Test-Path -LiteralPath $desktopStdoutPath) { Get-Content -Raw -LiteralPath $desktopStdoutPath } else { "" }
            $desktopStderr = if (Test-Path -LiteralPath $desktopStderrPath) { Get-Content -Raw -LiteralPath $desktopStderrPath } else { "" }
            ($desktopStdout + "`r`n" + $desktopStderr) | Set-Content -Encoding ASCII -Path $DesktopServiceBuildLogPath
            Remove-Item -LiteralPath $desktopStdoutPath, $desktopStderrPath -Force -ErrorAction SilentlyContinue
            if ($desktopProcess.ExitCode -eq 0 -and (Test-Path -LiteralPath $DesktopServiceKernelPath)) {
                $desktopServiceBuildStatus = "pass"
                $KernelPath = $DesktopServiceKernelPath
            } else {
                $desktopServiceBuildStatus = "blocked:desktop-service-build-exit-$($desktopProcess.ExitCode)"
            }
        } catch {
            $desktopServiceBuildStatus = "blocked:desktop-service-build-launch-failed"
        } finally {
            if ($null -eq $oldBackend) { Remove-Item Env:SIMPLE_OS_BUILD_BACKEND -ErrorAction SilentlyContinue } else { $env:SIMPLE_OS_BUILD_BACKEND = $oldBackend }
            if ($null -eq $oldSimpleLib) { Remove-Item Env:SIMPLE_LIB -ErrorAction SilentlyContinue } else { $env:SIMPLE_LIB = $oldSimpleLib }
            if ($null -eq $oldCc) { Remove-Item Env:CC -ErrorAction SilentlyContinue } else { $env:CC = $oldCc }
        }
    }
}

$diskImageBuildAttempted = $false
$diskImageBuildStatus = "not-requested"
$diskImageBuildExitCode = ""
$diskImageBuilderCompileExitCode = ""
$diskImageBuilderCompilerUsed = ""
$diskImageBuilderPathUsed = $DiskImageBuilderPath
$diskImageBuilderCompileLogPath = Join-Path $artifactDir "disk-image-builder-compile.stderr.log"
$diskImageBuilderCompileStdoutPath = Join-Path $artifactDir "disk-image-builder-compile.stdout.log"
$diskImageBuilderRunLogPath = Join-Path $artifactDir "disk-image-builder-run.stderr.log"
$diskImageBuilderRunStdoutPath = Join-Path $artifactDir "disk-image-builder-run.stdout.log"
if ($BuildDiskImage) {
    $diskImageBuildAttempted = $true
    if ([string]::IsNullOrWhiteSpace($DiskImageBuilderCompiler)) {
        $DiskImageBuilderCompiler = $BuildCc
    }
    $diskImageBuilderCompilerUsed = $DiskImageBuilderCompiler
    if ([string]::IsNullOrWhiteSpace($DiskImageBuilderCompiler) -or -not (Test-Path -LiteralPath $DiskImageBuilderCompiler)) {
        $diskImageBuildStatus = "blocked:missing-disk-image-builder-compiler"
    } elseif (-not (Test-Path -LiteralPath $DiskImageBuilderSource)) {
        $diskImageBuildStatus = "blocked:missing-disk-image-builder-source"
    } elseif (-not (Test-Path -LiteralPath $KernelPath)) {
        $diskImageBuildStatus = "blocked:missing-kernel-for-disk-image"
    } else {
        $builderDir = Split-Path -Parent $DiskImageBuilderPath
        if (-not [string]::IsNullOrWhiteSpace($builderDir)) {
            New-Item -ItemType Directory -Force -Path $builderDir | Out-Null
        }
        Remove-Item -LiteralPath $diskImageBuilderCompileLogPath, $diskImageBuilderCompileStdoutPath -Force -ErrorAction SilentlyContinue
        $compileProcess = Start-Process -FilePath $DiskImageBuilderCompiler -ArgumentList @($DiskImageBuilderSource, "-o", $DiskImageBuilderPath) -Wait -PassThru -NoNewWindow -RedirectStandardOutput $diskImageBuilderCompileStdoutPath -RedirectStandardError $diskImageBuilderCompileLogPath
        $diskImageBuilderCompileExitCode = "$($compileProcess.ExitCode)"
        if ($compileProcess.ExitCode -ne 0) {
            $diskImageBuildStatus = "blocked:disk-image-builder-compile-exit-$($compileProcess.ExitCode)"
        } else {
            Remove-Item -LiteralPath $diskImageBuilderRunLogPath, $diskImageBuilderRunStdoutPath -Force -ErrorAction SilentlyContinue
            $runProcess = Start-Process -FilePath $DiskImageBuilderPath -ArgumentList @($ImagePath, "riscv64", "64", $KernelPath) -Wait -PassThru -NoNewWindow -RedirectStandardOutput $diskImageBuilderRunStdoutPath -RedirectStandardError $diskImageBuilderRunLogPath
            $diskImageBuildExitCode = "$($runProcess.ExitCode)"
            if ($runProcess.ExitCode -eq 0 -and (Test-Path -LiteralPath $ImagePath)) {
                $diskImageBuildStatus = "pass"
            } else {
                $diskImageBuildStatus = "blocked:disk-image-build-exit-$($runProcess.ExitCode)"
            }
        }
    }
}

$kernelPresent = Test-Path -LiteralPath $KernelPath
$imagePresent = Test-Path -LiteralPath $ImagePath
$kernelCandidates = @($KernelPath, $canonicalKernelPath, $legacyKernelPath, $fpgaKernelPath) | Select-Object -Unique
$imageCandidates = @($ImagePath, $canonicalImagePath, $storageProbeImagePath) | Select-Object -Unique
$firstKernelCandidate = First-ExistingPath $kernelCandidates
$firstImageCandidate = First-ExistingPath $imageCandidates
$canonicalKernelPresent = Test-Path -LiteralPath $canonicalKernelPath
$legacyKernelPresent = Test-Path -LiteralPath $legacyKernelPath
$fpgaKernelPresent = Test-Path -LiteralPath $fpgaKernelPath
$canonicalImagePresent = Test-Path -LiteralPath $canonicalImagePath
$storageProbeImagePresent = Test-Path -LiteralPath $storageProbeImagePath
$liveBootAttempted = $false
$liveBootStatus = "not-requested"
$qemuExitStatus = "not-started"
$serialConsoleStatus = $(if ($qemuPresent -and $kernelPresent) { "blocked" } else { "missing" })
$sshBanner = ""
$sshProbeStatus = "missing"
$httpStatusCode = 0
$httpProbeStatus = "missing"
$gpuReadbackStatus = "missing"
$wmMarkerStatus = "missing"
$qmpStatus = "not-requested"
$screendumpStatus = "not-requested"
$screendumpNonblankStatus = "not-requested"
$launchError = ""
$qemuOutputStatus = "not-requested"

if ($RunLiveBoot) {
    $liveBootAttempted = $true
    if (-not $qemuPresent) {
        $liveBootStatus = "blocked:missing-qemu-system-riscv64"
    } elseif (-not $canonicalKernelPresent) {
        $liveBootStatus = "blocked:missing-desktop-smf-fs-kernel"
    } elseif (-not $canonicalImagePresent) {
        $liveBootStatus = "blocked:missing-fat32-riscv64-image"
    } else {
        Remove-Item -LiteralPath $SerialLogPath -Force -ErrorAction SilentlyContinue
        Remove-Item -LiteralPath $ScreendumpPath -Force -ErrorAction SilentlyContinue
        Remove-Item -LiteralPath $qemuStdoutPath, $qemuStderrPath -Force -ErrorAction SilentlyContinue
        $qemuArgs = @(
            "-machine", "virt",
            "-cpu", "rv64",
            "-m", "512M",
            "-display", "none",
            "-monitor", "none",
            "-qmp", "tcp:127.0.0.1:$QmpPort,server,nowait",
            "-bios", "default",
            "-global", "virtio-mmio.force-legacy=false",
            "-netdev", "user,id=rvnet,hostfwd=tcp::$SshPort-:22,hostfwd=tcp::$HttpPort-:8080",
            "-device", "virtio-net-pci,netdev=rvnet",
            "-device", "virtio-gpu-pci,disable-modern=on,disable-legacy=off",
            "-drive", "file=$ImagePath,if=none,id=rvdisk,format=raw",
            "-device", "virtio-blk-device,drive=rvdisk",
            "-kernel", $KernelPath,
            "-serial", "file:$SerialLogPath"
        )
        $qemuProcess = $null
        try {
            $qemuProcess = Start-Process -FilePath $QemuBinary -ArgumentList $qemuArgs -PassThru -WindowStyle Hidden -RedirectStandardOutput $qemuStdoutPath -RedirectStandardError $qemuStderrPath
            $qemuOutputStatus = "capturing"
            $liveBootStatus = "running"
            $qmpStatus = "requested"
            $deadline = (Get-Date).AddSeconds($BootTimeoutSeconds)
            while ((Get-Date) -lt $deadline) {
                if ($qemuProcess.HasExited) {
                    $qemuProcess.WaitForExit()
                    $qemuProcess.Refresh()
                    $exitCode = $qemuProcess.ExitCode
                    $qemuExitStatus = "exited:$exitCode"
                    if ($exitCode -ne 0) {
                        $liveBootStatus = "blocked:qemu-exit-$exitCode"
                    }
                    break
                }
                $serialText = Read-TextFileOrEmpty $SerialLogPath
                if ((Test-TextContains $serialText "SIMPLEOS_RISCV_SMF_FS_PASS") -or
                    (Test-TextContains $serialText "Network service ready") -or
                    (Test-TextContains $serialText "Bootstrap TCP shim bound on 0.0.0.0:8080")) {
                    $serialConsoleStatus = "pass"
                }
                if ((Test-TextContains $serialText "Display service ready") -and $gpuReadbackStatus -ne "pass") {
                    $gpuReadbackStatus = "blocked:display-ready-no-readback"
                    if ($screendumpStatus -eq "not-requested") {
                        $screendumpStatus = Invoke-QmpScreendump $QmpPort $ScreendumpPath $ProbeTimeoutMs
                        $screendumpNonblankStatus = Test-PpmNonblank $ScreendumpPath
                        if ($screendumpStatus -eq "pass" -and $screendumpNonblankStatus -eq "pass") {
                            $gpuReadbackStatus = "pass"
                            $qmpStatus = "pass"
                        } else {
                            $qmpStatus = $screendumpStatus
                        }
                    }
                }
                if ((Test-TextContains $serialText "[WM] Glass desktop rendered!") -or
                    (Test-TextContains $serialText "SimpleOS Web WM") -or
                    (Test-TextContains $serialText "[desktop-e2e]")) {
                    $wmMarkerStatus = "blocked:wm-marker-without-structured-readback"
                    if ($gpuReadbackStatus -eq "pass") {
                        $wmMarkerStatus = "pass"
                    }
                }
                $observedSshBanner = Read-SshBanner $SshPort $ProbeTimeoutMs
                if ($observedSshBanner -ne "") {
                    $sshBanner = $observedSshBanner
                    $sshProbeStatus = "pass"
                }
                $observedHttpStatusCode = Invoke-HttpStatusCode $HttpPort $ProbeTimeoutMs
                if ($observedHttpStatusCode -eq 200) {
                    $httpStatusCode = $observedHttpStatusCode
                    $httpProbeStatus = "pass"
                } elseif ($httpProbeStatus -ne "pass") {
                    $httpStatusCode = $observedHttpStatusCode
                }
                if (($serialConsoleStatus -eq "pass") -and ($sshProbeStatus -eq "pass") -and ($httpProbeStatus -eq "pass")) {
                    $liveBootStatus = "probed"
                    break
                }
                Start-Sleep -Milliseconds 500
            }
            if ($liveBootStatus -eq "running") {
                $liveBootStatus = "blocked:boot-timeout"
            }
            if ($qemuExitStatus -eq "not-started" -and $qemuProcess -and $qemuProcess.HasExited) {
                $qemuProcess.WaitForExit()
                $qemuProcess.Refresh()
                $exitCode = $qemuProcess.ExitCode
                $qemuExitStatus = "exited:$exitCode"
                if ($exitCode -ne 0 -and $liveBootStatus -eq "running") {
                    $liveBootStatus = "blocked:qemu-exit-$exitCode"
                }
            } elseif ($qemuExitStatus -eq "not-started" -and $qemuProcess) {
                $qemuExitStatus = "running"
            }
            $finalSerialText = Read-TextFileOrEmpty $SerialLogPath
            if ((Test-TextContains $finalSerialText "SIMPLEOS_RISCV_SMF_FS_PASS") -or
                (Test-TextContains $finalSerialText "TEST PASSED")) {
                $serialConsoleStatus = "pass"
                if ($liveBootStatus -eq "blocked:boot-timeout") {
                    $liveBootStatus = "guest-exited-before-service-probes"
                }
            }
            if ((Test-TextContains $finalSerialText "SMF_WM_GUI_LAUNCH_OK") -or
                (Test-TextContains $finalSerialText "NATIVE_GUI_PROCESS_RENDER_OK") -or
                (Test-TextContains $finalSerialText "[WM] Glass desktop rendered!") -or
                (Test-TextContains $finalSerialText "SimpleOS Web WM") -or
                (Test-TextContains $finalSerialText "[desktop-e2e]")) {
                if ($gpuReadbackStatus -eq "pass") {
                    $wmMarkerStatus = "pass"
                } else {
                    $wmMarkerStatus = "blocked:wm-marker-without-structured-readback"
                }
            }
            if ($screendumpStatus -eq "pass" -and $screendumpNonblankStatus -eq "pass") {
                $gpuReadbackStatus = "pass"
                $qmpStatus = "pass"
                if ((Test-TextContains $finalSerialText "SMF_WM_GUI_LAUNCH_OK") -or
                    (Test-TextContains $finalSerialText "NATIVE_GUI_PROCESS_RENDER_OK") -or
                    (Test-TextContains $finalSerialText "[WM] Glass desktop rendered!") -or
                    (Test-TextContains $finalSerialText "SimpleOS Web WM") -or
                    (Test-TextContains $finalSerialText "[desktop-e2e]")) {
                    $wmMarkerStatus = "pass"
                }
            }
        } catch {
            $liveBootStatus = "blocked:qemu-launch-failed"
            $qemuExitStatus = "launch-error"
            $launchError = $_.Exception.Message
            $qemuOutputStatus = "blocked:qemu-launch-failed"
        } finally {
            if ($qemuProcess -and (-not $qemuProcess.HasExited) -and (-not $KeepQemu)) {
                Stop-Process -Id $qemuProcess.Id -Force -ErrorAction SilentlyContinue
                $qemuExitStatus = "stopped"
            }
            if ((Test-Path -LiteralPath $qemuStdoutPath) -or (Test-Path -LiteralPath $qemuStderrPath)) {
                if ($qemuOutputStatus -eq "capturing") {
                    $qemuOutputStatus = "pass"
                }
            } elseif ($qemuOutputStatus -eq "capturing") {
                $qemuOutputStatus = "missing"
            }
        }
    }
}

Write-Row $rows "simpleos_qemu_rv64_evidence_wrapper" "check-simpleos-qemu-rv64-desktop-evidence.ps1"
Write-Row $rows "simpleos_qemu_rv64_live_boot_requested" $(if ($RunLiveBoot) { "true" } else { "false" })
Write-Row $rows "simpleos_qemu_rv64_live_boot_status" "$liveBootStatus"
Write-Row $rows "simpleos_qemu_rv64_qemu_exit_status" "$qemuExitStatus"
Write-Row $rows "simpleos_qemu_rv64_artifact_dir" "$ArtifactDir"
Write-Row $rows "simpleos_qemu_rv64_serial_log_path" "$SerialLogPath"
Write-Row $rows "simpleos_qemu_rv64_qmp_port" "$QmpPort"
Write-Row $rows "simpleos_qemu_rv64_qmp_status" "$qmpStatus"
Write-Row $rows "simpleos_qemu_rv64_screendump_path" "$ScreendumpPath"
Write-Row $rows "simpleos_qemu_rv64_screendump_status" "$screendumpStatus"
Write-Row $rows "simpleos_qemu_rv64_screendump_nonblank_status" "$screendumpNonblankStatus"
Write-Row $rows "simpleos_qemu_rv64_stdout_path" "$qemuStdoutPath"
Write-Row $rows "simpleos_qemu_rv64_stderr_path" "$qemuStderrPath"
Write-Row $rows "simpleos_qemu_rv64_process_output_status" "$qemuOutputStatus"
if (-not [string]::IsNullOrWhiteSpace($launchError)) {
    Write-Row $rows "simpleos_qemu_rv64_launch_error" "$launchError"
}
Write-Row $rows "simpleos_qemu_rv64_qemu_binary" "$QemuBinary"
Write-Row $rows "simpleos_qemu_rv64_qemu_binary_status" $(if ($qemuPresent) { "pass" } else { "blocked" })
Write-Row $rows "simpleos_qemu_rv64_build_attempted" $(if ($buildAttempted) { "true" } else { "false" })
Write-Row $rows "simpleos_qemu_rv64_build_status" "$buildStatus"
Write-Row $rows "simpleos_qemu_rv64_build_exit_code" "$buildExitCode"
Write-Row $rows "simpleos_qemu_rv64_native_build_exit_code" "$buildNativeExitCode"
Write-Row $rows "simpleos_qemu_rv64_build_command" "$buildCommand"
Write-Row $rows "simpleos_qemu_rv64_build_log_path" "$BuildLogPath"
Write-Row $rows "simpleos_qemu_rv64_build_backend" $(if ([string]::IsNullOrWhiteSpace($BuildBackend)) { "default" } else { "$BuildBackend" })
Write-Row $rows "simpleos_qemu_rv64_nested_simple_binary" "$nestedSimpleBinaryUsed"
Write-Row $rows "simpleos_qemu_rv64_nested_simple_binary_source" "$nestedSimpleBinarySource"
Write-Row $rows "simpleos_qemu_rv64_build_cc" "$buildCcUsed"
Write-Row $rows "simpleos_qemu_rv64_build_cc_source" "$buildCcSource"
if (-not [string]::IsNullOrWhiteSpace($buildError)) {
    Write-Row $rows "simpleos_qemu_rv64_build_error" "$buildError"
}
Write-Row $rows "simpleos_qemu_rv64_desktop_service_build_attempted" $(if ($desktopServiceBuildAttempted) { "true" } else { "false" })
Write-Row $rows "simpleos_qemu_rv64_desktop_service_build_status" "$desktopServiceBuildStatus"
Write-Row $rows "simpleos_qemu_rv64_desktop_service_build_exit_code" "$desktopServiceBuildExitCode"
Write-Row $rows "simpleos_qemu_rv64_desktop_service_build_command" "$desktopServiceBuildCommand"
Write-Row $rows "simpleos_qemu_rv64_desktop_service_build_log_path" "$DesktopServiceBuildLogPath"
Write-Row $rows "simpleos_qemu_rv64_desktop_service_entry" "$DesktopServiceEntry"
Write-Row $rows "simpleos_qemu_rv64_desktop_service_kernel_path" "$DesktopServiceKernelPath"
Write-Row $rows "simpleos_qemu_rv64_disk_image_build_attempted" $(if ($diskImageBuildAttempted) { "true" } else { "false" })
Write-Row $rows "simpleos_qemu_rv64_disk_image_build_status" "$diskImageBuildStatus"
Write-Row $rows "simpleos_qemu_rv64_disk_image_build_exit_code" "$diskImageBuildExitCode"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_compile_exit_code" "$diskImageBuilderCompileExitCode"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_compiler" "$diskImageBuilderCompilerUsed"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_path" "$diskImageBuilderPathUsed"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_compile_log_path" "$diskImageBuilderCompileLogPath"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_compile_stdout_path" "$diskImageBuilderCompileStdoutPath"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_run_log_path" "$diskImageBuilderRunLogPath"
Write-Row $rows "simpleos_qemu_rv64_disk_image_builder_run_stdout_path" "$diskImageBuilderRunStdoutPath"
Write-Row $rows "simpleos_qemu_rv64_kernel_path" "$KernelPath"
Write-Row $rows "simpleos_qemu_rv64_kernel_status" $(if ($kernelPresent) { "pass" } else { "blocked" })
Write-Row $rows "simpleos_qemu_rv64_canonical_kernel_path" "$canonicalKernelPath"
Write-Row $rows "simpleos_qemu_rv64_canonical_kernel_status" $(if ($canonicalKernelPresent) { "pass" } else { "blocked" })
Write-Row $rows "simpleos_qemu_rv64_legacy_kernel_path" "$legacyKernelPath"
Write-Row $rows "simpleos_qemu_rv64_legacy_kernel_status" $(if ($legacyKernelPresent) { "present-smoke-only" } else { "missing" })
Write-Row $rows "simpleos_qemu_rv64_fpga_kernel_path" "$fpgaKernelPath"
Write-Row $rows "simpleos_qemu_rv64_fpga_kernel_status" $(if ($fpgaKernelPresent) { "present-fpga-only" } else { "missing" })
Write-Row $rows "simpleos_qemu_rv64_kernel_candidate_paths" (Join-Values $kernelCandidates)
Write-Row $rows "simpleos_qemu_rv64_kernel_candidate_status" $(if ([string]::IsNullOrWhiteSpace($firstKernelCandidate)) { "none" } else { "found:$firstKernelCandidate" })
Write-Row $rows "simpleos_qemu_rv64_image_path" "$ImagePath"
Write-Row $rows "simpleos_qemu_rv64_image_status" $(if ($imagePresent) { "pass" } else { "blocked" })
Write-Row $rows "simpleos_qemu_rv64_canonical_image_path" "$canonicalImagePath"
Write-Row $rows "simpleos_qemu_rv64_canonical_image_status" $(if ($canonicalImagePresent) { "pass" } else { "blocked" })
Write-Row $rows "simpleos_qemu_rv64_storage_probe_image_path" "$storageProbeImagePath"
Write-Row $rows "simpleos_qemu_rv64_storage_probe_image_status" $(if ($storageProbeImagePresent) { "present-diagnostic-only" } else { "missing" })
Write-Row $rows "simpleos_qemu_rv64_image_candidate_paths" (Join-Values $imageCandidates)
Write-Row $rows "simpleos_qemu_rv64_image_candidate_status" $(if ([string]::IsNullOrWhiteSpace($firstImageCandidate)) { "none" } else { "found:$firstImageCandidate" })
Write-Row $rows "simpleos_qemu_rv64_build_hint" "bin/simple os build --arch=riscv64"
Write-Row $rows "simpleos_qemu_rv64_ssh_host_port" "$SshPort"
Write-Row $rows "simpleos_qemu_rv64_http_host_port" "$HttpPort"
if (-not $RunLiveBoot) {
    $sshOpen = Test-TcpPort "127.0.0.1" $SshPort $ProbeTimeoutMs
    $httpOpen = Test-TcpPort "127.0.0.1" $HttpPort $ProbeTimeoutMs
    $sshBanner = $(if ($sshOpen) { "tcp-open-banner-unread" } else { "" })
    $sshProbeStatus = $(if ($sshOpen) { "blocked" } else { "missing" })
    $httpStatusCode = 0
    $httpProbeStatus = $(if ($httpOpen) { "blocked" } else { "missing" })
}

Write-Row $rows "simpleos_qemu_serial_console_status" "$serialConsoleStatus"
Write-Row $rows "simpleos_qemu_rv64_ssh_banner" "$sshBanner"
Write-Row $rows "simpleos_qemu_rv64_ssh_probe_status" "$sshProbeStatus"
Write-Row $rows "simpleos_qemu_rv64_http_status_code" "$httpStatusCode"
Write-Row $rows "simpleos_qemu_rv64_http_probe_status" "$httpProbeStatus"
Write-Row $rows "simpleos_qemu_gpu_readback_status" "$gpuReadbackStatus"
Write-Row $rows "simpleos_qemu_wm_marker_status" "$wmMarkerStatus"

if (-not $qemuPresent) {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-qemu-system-riscv64"
} elseif (-not $canonicalKernelPresent) {
    if ($legacyKernelPresent) {
        Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-desktop-smf-fs-kernel;legacy-smoke-kernel-present"
    } elseif ($fpgaKernelPresent) {
        Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-desktop-smf-fs-kernel;fpga-kernel-present"
    } else {
        Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-desktop-smf-fs-kernel"
    }
} elseif (-not $kernelPresent) {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-kernel"
} elseif (-not $canonicalImagePresent) {
    if ($storageProbeImagePresent) {
        Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-fat32-riscv64-image;storage-probe-image-present"
    } else {
        Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-fat32-riscv64-image"
    }
} elseif (-not $imagePresent) {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-disk-image"
} elseif ($RunLiveBoot -and $serialConsoleStatus -ne "pass") {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "$liveBootStatus"
} elseif ($RunLiveBoot -and $sshProbeStatus -ne "pass") {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-live-ssh-probe"
} elseif ($RunLiveBoot -and $httpProbeStatus -ne "pass") {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-live-http-probe"
} elseif ($RunLiveBoot -and $gpuReadbackStatus -ne "pass") {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-live-gpu-readback"
} elseif ($RunLiveBoot -and $wmMarkerStatus -ne "pass") {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "missing-live-wm-marker"
} elseif ($RunLiveBoot) {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "pass"
} else {
    Write-Row $rows "simpleos_qemu_rv64_blocker" "live-boot-not-run-by-preflight"
}

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
$rows | ForEach-Object { Write-Output $_ }
Write-Output "simpleos_qemu_rv64_evidence_path=$EvidencePath"

if ($RunLiveBoot -and
    $serialConsoleStatus -eq "pass" -and
    $sshProbeStatus -eq "pass" -and
    $httpStatusCode -eq 200 -and
    $httpProbeStatus -eq "pass" -and
    $gpuReadbackStatus -eq "pass" -and
    $wmMarkerStatus -eq "pass") {
    exit 0
}

exit 1
