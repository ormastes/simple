param(
    [string]$EvidencePath = "build/simpleos_multiconfig_live_evidence/wm-host-compare.env",
    [string]$BaseEvidencePath = "",
    [string]$QemuPpmPath = "build/os/systest/qemu-riscv64-desktop/qemu-screendump.ppm",
    [string]$HostPpmPath = "build/os/systest/qemu-riscv64-desktop/host-wm.ppm",
    [string]$QemuRenderdocLogPath = "build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log",
    [string]$HostRenderdocLogPath = "build/os/systest/qemu-riscv64-desktop/host-wm-renderdoc.log",
    [string]$SimpleRdcPath = "build/os/systest/qemu-riscv64-desktop/simpleos-wm.rdc",
    [string]$CaptureLogPath = "build/os/systest/qemu-riscv64-desktop/renderdoc-capture.log",
    [string]$WmSceneName = "simpleos-desktop-four-windows",
    [string]$RenderdocSceneName = "vulkan-engine2d",
    [string]$FocusId = "main",
    [int]$WindowCount = 1,
    [switch]$AttemptHostWmCapture,
    [string]$SimpleBinary = "src\compiler_rust\target\debug\simple.exe",
    [string]$HostCaptureEntry = "src/os/compositor/hosted_wm_capture_evidence.spl",
    [string]$HostCaptureLogPath = "build/simpleos_multiconfig_live_evidence/host-wm-capture.log",
    [int]$HostCaptureTimeoutSeconds = 20
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)

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
$BaseEvidencePath = Resolve-RepoPath $BaseEvidencePath
$QemuPpmPath = Resolve-RepoPath $QemuPpmPath
$HostPpmPath = Resolve-RepoPath $HostPpmPath
$QemuRenderdocLogPath = Resolve-RepoPath $QemuRenderdocLogPath
$HostRenderdocLogPath = Resolve-RepoPath $HostRenderdocLogPath
$SimpleRdcPath = Resolve-RepoPath $SimpleRdcPath
$CaptureLogPath = Resolve-RepoPath $CaptureLogPath
$SimpleBinary = Resolve-RepoPath $SimpleBinary
$HostCaptureEntry = Resolve-RepoPath $HostCaptureEntry
$HostCaptureLogPath = Resolve-RepoPath $HostCaptureLogPath

function Write-Row($rows, [string]$key, [string]$value) {
    $prefix = "$key="
    for ($i = $rows.Count - 1; $i -ge 0; $i--) {
        if ($rows[$i].StartsWith($prefix)) {
            $rows.RemoveAt($i)
        }
    }
    $rows.Add("$key=$value") | Out-Null
}

function Test-FileNonEmpty([string]$path) {
    if ([string]::IsNullOrWhiteSpace($path) -or -not (Test-Path -LiteralPath $path)) {
        return $false
    }
    return ((Get-Item -LiteralPath $path).Length -gt 0)
}

function Read-RdcMagic([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return ""
    }
    $stream = [System.IO.File]::OpenRead((Resolve-Path -LiteralPath $path))
    try {
        $buffer = New-Object byte[] 4
        $count = $stream.Read($buffer, 0, 4)
        if ($count -lt 4) {
            return ""
        }
        return [System.Text.Encoding]::ASCII.GetString($buffer, 0, 4)
    } finally {
        $stream.Close()
    }
}

function Read-LogField([string]$text, [string[]]$keys) {
    foreach ($key in $keys) {
        $escaped = [regex]::Escape($key)
        $patterns = @(
            "(?m)^${escaped}=([^\r\n]+)",
            "(?m)^${escaped}:\s*([^\r\n]+)",
            "(?m)\b${escaped}=([^\s\r\n]+)"
        )
        foreach ($pattern in $patterns) {
            $m = [regex]::Match($text, $pattern)
            if ($m.Success -and $m.Groups.Count -gt 1) {
                return $m.Groups[1].Value.Trim()
            }
        }
    }
    return ""
}

function Read-RenderdocLogEvidence([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return @{ status = "missing"; scene = ""; backend = ""; capture_mode = ""; rdc_magic = ""; reason = "missing" }
    }
    $text = Get-Content -Raw -LiteralPath $path
    $scene = Read-LogField $text @("simpleos_wm_compare_scene", "simpleos_wm_scene", "wm_scene", "scene")
    $backend = Read-LogField $text @("simpleos_renderdoc_simple_runtime_backend", "runtime_backend", "backend")
    $captureMode = Read-LogField $text @("simpleos_renderdoc_capture_mode", "capture_mode", "mode")
    $rdcMagic = Read-LogField $text @("simpleos_renderdoc_rdc_magic", "rdc_magic")
    if ($rdcMagic -eq "" -and $text.Contains("RDOC")) {
        $rdcMagic = "RDOC"
    }
    return @{ status = "pass"; scene = $scene; backend = $backend; capture_mode = $captureMode; rdc_magic = $rdcMagic; reason = "pass" }
}

function Compare-RenderdocLogs([string]$qemuLogPath, [string]$hostLogPath, [string]$wmSceneName) {
    $qemuLog = Read-RenderdocLogEvidence $qemuLogPath
    $hostLog = Read-RenderdocLogEvidence $hostLogPath
    if ($qemuLog.status -ne "pass" -and $hostLog.status -ne "pass") {
        return @{ status = "missing"; reason = "missing-qemu-and-host-renderdoc-logs"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.status -ne "pass") {
        return @{ status = "missing"; reason = "missing-qemu-renderdoc-log"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($hostLog.status -ne "pass") {
        return @{ status = "missing"; reason = "missing-host-renderdoc-log"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.scene -eq "" -or $hostLog.scene -eq "") {
        return @{ status = "blocked"; reason = "missing-renderdoc-log-scene"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.scene -ne $hostLog.scene) {
        return @{ status = "blocked"; reason = "renderdoc-log-scene-mismatch"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.scene -ne $wmSceneName) {
        return @{ status = "blocked"; reason = "renderdoc-log-unexpected-scene"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.backend -ne "vulkan" -or $hostLog.backend -ne "vulkan") {
        return @{ status = "blocked"; reason = "renderdoc-log-missing-vulkan-backend"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.capture_mode -ne "capture-simple" -or $hostLog.capture_mode -ne "capture-simple") {
        return @{ status = "blocked"; reason = "renderdoc-log-missing-capture-simple-mode"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    if ($qemuLog.rdc_magic -ne "RDOC" -or $hostLog.rdc_magic -ne "RDOC") {
        return @{ status = "blocked"; reason = "renderdoc-log-missing-rdoc-magic"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
    }
    return @{ status = "pass"; reason = "pass"; mode = "structured-renderdoc-log-compare"; qemu = $qemuLog; host = $hostLog }
}

function Get-FileSizeText([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return "0"
    }
    return ((Get-Item -LiteralPath $path).Length).ToString()
}

function Read-Ppm([string]$path) {
    if (-not (Test-FileNonEmpty $path)) {
        return @{ status = "missing"; width = 0; height = 0; body = @(); reason = "missing" }
    }
    $bytes = [System.IO.File]::ReadAllBytes((Resolve-Path -LiteralPath $path))
    if ($bytes.Length -lt 16 -or $bytes[0] -ne [byte][char]'P') {
        return @{ status = "blocked"; width = 0; height = 0; body = @(); reason = "not-ppm" }
    }
    if ($bytes[1] -eq [byte][char]'3') {
        $text = [System.Text.Encoding]::ASCII.GetString($bytes)
        $cleanLines = [System.Collections.Generic.List[string]]::new()
        foreach ($line in ($text -split "`n")) {
            $comment = $line.IndexOf("#")
            if ($comment -ge 0) {
                $line = $line.Substring(0, $comment)
            }
            if (-not [string]::IsNullOrWhiteSpace($line)) {
                $cleanLines.Add($line) | Out-Null
            }
        }
        $tokens = (($cleanLines -join " ") -split "\s+") | Where-Object { $_ -ne "" }
        if ($tokens.Count -lt 4 -or $tokens[0] -ne "P3") {
            return @{ status = "blocked"; width = 0; height = 0; body = @(); reason = "bad-p3-header" }
        }
        $width = [int]$tokens[1]
        $height = [int]$tokens[2]
        $max = [int]$tokens[3]
        if ($width -le 0 -or $height -le 0 -or $max -le 0) {
            return @{ status = "blocked"; width = $width; height = $height; body = @(); reason = "bad-p3-dimensions" }
        }
        $expected = $width * $height * 3
        if (($tokens.Count - 4) -lt $expected) {
            return @{ status = "blocked"; width = $width; height = $height; body = @(); reason = "short-p3-body" }
        }
        $body = New-Object byte[] $expected
        for ($j = 0; $j -lt $expected; $j++) {
            $v = [int]$tokens[$j + 4]
            if ($v -lt 0) { $v = 0 }
            if ($v -gt $max) { $v = $max }
            $body[$j] = [byte][Math]::Round(($v * 255.0) / $max)
        }
        $first = $body[0]
        $nonblank = $false
        foreach ($b in $body) {
            if ($b -ne $first) {
                $nonblank = $true
                break
            }
        }
        if (-not $nonblank) {
            return @{ status = "blocked"; width = $width; height = $height; body = $body; reason = "blank-ppm" }
        }
        return @{ status = "pass"; width = $width; height = $height; body = $body; reason = "pass" }
    }
    if ($bytes[1] -ne [byte][char]'6') {
        return @{ status = "blocked"; width = 0; height = 0; body = @(); reason = "unsupported-ppm-magic" }
    }
    $tokens = [System.Collections.Generic.List[string]]::new()
    $token = ""
    $i = 2
    while ($i -lt $bytes.Length -and $tokens.Count -lt 3) {
        $ch = [char]$bytes[$i]
        if ($ch -eq '#') {
            while ($i -lt $bytes.Length -and [char]$bytes[$i] -ne "`n") {
                $i++
            }
        } elseif ([char]::IsWhiteSpace($ch)) {
            if ($token -ne "") {
                $tokens.Add($token) | Out-Null
                $token = ""
            }
        } else {
            $token += $ch
        }
        $i++
    }
    if ($token -ne "" -and $tokens.Count -lt 3) {
        $tokens.Add($token) | Out-Null
    }
    if ($tokens.Count -lt 3) {
        return @{ status = "blocked"; width = 0; height = 0; body = @(); reason = "bad-ppm-header" }
    }
    while ($i -lt $bytes.Length -and [char]::IsWhiteSpace([char]$bytes[$i])) {
        $i++
    }
    $bodyLen = $bytes.Length - $i
    if ($bodyLen -le 0) {
        return @{ status = "blocked"; width = [int]$tokens[0]; height = [int]$tokens[1]; body = @(); reason = "empty-ppm-body" }
    }
    $body = New-Object byte[] $bodyLen
    [Array]::Copy($bytes, $i, $body, 0, $bodyLen)
    $first = $body[0]
    $nonblank = $false
    foreach ($b in $body) {
        if ($b -ne $first) {
            $nonblank = $true
            break
        }
    }
    if (-not $nonblank) {
        return @{ status = "blocked"; width = [int]$tokens[0]; height = [int]$tokens[1]; body = $body; reason = "blank-ppm" }
    }
    return @{ status = "pass"; width = [int]$tokens[0]; height = [int]$tokens[1]; body = $body; reason = "pass" }
}

function Count-Mismatches($a, $b) {
    if ($a.status -ne "pass" -or $b.status -ne "pass") {
        return -1
    }
    if ($a.width -ne $b.width -or $a.height -ne $b.height) {
        return -1
    }
    if ($a.body.Length -ne $b.body.Length) {
        return -1
    }
    $count = 0
    for ($i = 0; $i -lt $a.body.Length; $i++) {
        if ($a.body[$i] -ne $b.body[$i]) {
            $count++
        }
    }
    return $count
}

function Test-QemuGpuTestPattern($ppm) {
    if ($ppm.status -ne "pass" -or $ppm.width -ne 320 -or $ppm.height -ne 240) {
        return $false
    }
    $samples = @(
        @(0, 0),
        @(1, 0),
        @(0, 1),
        @(48, 68),
        @(319, 239)
    )
    foreach ($sample in $samples) {
        $x = [int]$sample[0]
        $y = [int]$sample[1]
        $idx = (($y * $ppm.width) + $x) * 3
        if (($idx + 2) -ge $ppm.body.Length) {
            return $false
        }
        $expectedR = [byte]($x -band 0xff)
        $expectedG = [byte]($y -band 0xff)
        $expectedB = [byte](($x -bxor $y) -band 0xff)
        if ($ppm.body[$idx] -ne $expectedR -or $ppm.body[$idx + 1] -ne $expectedG -or $ppm.body[$idx + 2] -ne $expectedB) {
            return $false
        }
    }
    return $true
}

function Test-WmRectScene($ppm) {
    if ($ppm.status -ne "pass" -or $ppm.width -ne 320 -or $ppm.height -ne 240) {
        return $false
    }
    $samples = @(
        @(0, 0, 0x10, 0x18, 0x20),
        @(0, 42, 0x34, 0x98, 0xdb),
        @(18, 66, 0x20, 0x50, 0xa0),
        @(30, 75, 0xe7, 0x4c, 0x3c),
        @(36, 114, 0x22, 0xc5, 0x5e),
        @(256, 205, 0x34, 0x98, 0xdb)
    )
    foreach ($sample in $samples) {
        $x = [int]$sample[0]
        $y = [int]$sample[1]
        $idx = (($y * $ppm.width) + $x) * 3
        if (($idx + 2) -ge $ppm.body.Length) {
            return $false
        }
        if ($ppm.body[$idx] -ne [byte]$sample[2] -or $ppm.body[$idx + 1] -ne [byte]$sample[3] -or $ppm.body[$idx + 2] -ne [byte]$sample[4]) {
            return $false
        }
    }
    return $true
}

function Get-CaptureKind($ppm, [string]$source) {
    if ($ppm.status -ne "pass") {
        return "missing"
    }
    if ($source -eq "qemu" -and (Test-QemuGpuTestPattern $ppm)) {
        return "qemu-virtio-gpu-test-pattern"
    }
    if ($source -eq "qemu" -and (Test-WmRectScene $ppm)) {
        return "qemu-wm-rect-scene"
    }
    if ($source -eq "host" -and (Test-WmRectScene $ppm)) {
        return "hosted-wm-rect-scene"
    }
    if ($source -eq "host" -and $ppm.width -eq 16 -and $ppm.height -eq 16) {
        return "hosted-wm-diagnostic-crop"
    }
    return "unknown-nonblank-ppm"
}

function Get-ArgbDiffReason($qemu, $hostCapture, [int]$mismatchCount, [string]$qemuKind, [string]$hostKind) {
    if ($qemu.status -ne "pass") {
        return "missing-qemu-ppm:$($qemu.reason)"
    }
    if ($hostCapture.status -ne "pass") {
        return "missing-host-ppm:$($hostCapture.reason)"
    }
    if ($qemu.width -ne $hostCapture.width -or $qemu.height -ne $hostCapture.height) {
        if ($qemuKind -eq "qemu-virtio-gpu-test-pattern" -and $hostKind -eq "hosted-wm-diagnostic-crop") {
            return "qemu-gpu-test-pattern-not-wm-scene"
        }
        return "dimension-mismatch:qemu-${($qemu.width)}x${($qemu.height)}:host-${($hostCapture.width)}x${($hostCapture.height)}"
    }
    if ($mismatchCount -lt 0) {
        return "body-mismatch"
    }
    if ($mismatchCount -gt 0) {
        return "pixel-mismatch:$mismatchCount"
    }
    return "pass"
}

function Convert-HexColorToRgb([string]$hex) {
    $trimmed = $hex.Trim()
    if ($trimmed.Length -ne 6) {
        throw "bad RGB hex color: $hex"
    }
    return @(
        [Convert]::ToByte($trimmed.Substring(0, 2), 16),
        [Convert]::ToByte($trimmed.Substring(2, 2), 16),
        [Convert]::ToByte($trimmed.Substring(4, 2), 16)
    )
}

function Fill-RgbRect([byte[]]$body, [int]$width, [int]$height, [int]$x, [int]$y, [int]$w, [int]$h, [byte[]]$rgb) {
    if ($x -lt 0 -or $y -lt 0 -or $w -le 0 -or $h -le 0) {
        return
    }
    $xEnd = [Math]::Min($width, $x + $w)
    $yEnd = [Math]::Min($height, $y + $h)
    for ($py = $y; $py -lt $yEnd; $py++) {
        for ($px = $x; $px -lt $xEnd; $px++) {
            $idx = (($py * $width) + $px) * 3
            $body[$idx] = $rgb[0]
            $body[$idx + 1] = $rgb[1]
            $body[$idx + 2] = $rgb[2]
        }
    }
}

function Write-RectScenePpmCapture([string[]]$lines, [string]$capturePath) {
    if ($lines.Count -lt 4 -or $lines[0].Trim() -ne "SIMPLE_WM_RECT_PPM_V1") {
        return $false
    }
    $width = [int]$lines[1].Trim()
    $height = [int]$lines[2].Trim()
    if ($width -le 0 -or $height -le 0) {
        return $false
    }
    $body = New-Object byte[] ($width * $height * 3)
    $bg = @(0, 0, 0)
    foreach ($line in $lines) {
        $parts = ($line.Trim() -split "\s+") | Where-Object { $_ -ne "" }
        if ($parts.Count -eq 2 -and $parts[0] -eq "BG") {
            $bg = Convert-HexColorToRgb $parts[1]
        }
    }
    Fill-RgbRect $body $width $height 0 0 $width $height ([byte[]]$bg)
    foreach ($line in $lines) {
        $parts = ($line.Trim() -split "\s+") | Where-Object { $_ -ne "" }
        if ($parts.Count -eq 6 -and $parts[0] -eq "RECT") {
            $rgb = Convert-HexColorToRgb $parts[5]
            Fill-RgbRect $body $width $height ([int]$parts[1]) ([int]$parts[2]) ([int]$parts[3]) ([int]$parts[4]) ([byte[]]$rgb)
        }
    }
    $captureDir = Split-Path -Parent $capturePath
    if (-not [string]::IsNullOrWhiteSpace($captureDir)) {
        New-Item -ItemType Directory -Force -Path $captureDir | Out-Null
    }
    $header = [System.Text.Encoding]::ASCII.GetBytes("P6`n$width $height`n255`n")
    $bytes = New-Object byte[] ($header.Length + $body.Length)
    [Array]::Copy($header, 0, $bytes, 0, $header.Length)
    [Array]::Copy($body, 0, $bytes, $header.Length, $body.Length)
    [System.IO.File]::WriteAllBytes($capturePath, $bytes)
    return (Test-FileNonEmpty $capturePath)
}

function Write-StdoutPpmCapture([string]$stdout, [string]$capturePath) {
    $begin = "SIMPLE_HOSTED_WM_PPM_BEGIN"
    $end = "SIMPLE_HOSTED_WM_PPM_END"
    $start = $stdout.IndexOf($begin)
    if ($start -lt 0) {
        return $false
    }
    $afterStart = $start + $begin.Length
    $finish = $stdout.IndexOf($end, $afterStart)
    if ($finish -lt 0) {
        return $false
    }
    $ppm = $stdout.Substring($afterStart, $finish - $afterStart).Trim()
    $lines = @($ppm -split "`r?`n" | Where-Object { $_.Trim() -ne "" })
    if ($lines.Count -gt 0 -and $lines[0].Trim() -eq "SIMPLE_WM_RECT_PPM_V1") {
        return Write-RectScenePpmCapture $lines $capturePath
    }
    if (-not $ppm.StartsWith("P3")) {
        return $false
    }
    $captureDir = Split-Path -Parent $capturePath
    if (-not [string]::IsNullOrWhiteSpace($captureDir)) {
        New-Item -ItemType Directory -Force -Path $captureDir | Out-Null
    }
    $ppm | Set-Content -Encoding ASCII -Path $capturePath
    return (Test-FileNonEmpty $capturePath)
}

function Invoke-HostWmCapture([string]$simpleBinary, [string]$entryPath, [string]$capturePath, [string]$logPath) {
    $logDir = Split-Path -Parent $logPath
    if (-not [string]::IsNullOrWhiteSpace($logDir)) {
        New-Item -ItemType Directory -Force -Path $logDir | Out-Null
    }
    $captureDir = Split-Path -Parent $capturePath
    if (-not [string]::IsNullOrWhiteSpace($captureDir)) {
        New-Item -ItemType Directory -Force -Path $captureDir | Out-Null
    }
    Remove-Item -LiteralPath $logPath -Force -ErrorAction SilentlyContinue
    if (-not (Test-Path -LiteralPath $simpleBinary)) {
        "missing Simple binary: $simpleBinary" | Set-Content -Encoding ASCII -Path $logPath
        return @{ attempted = "true"; status = "blocked:missing-simple-binary"; exit_code = ""; log_path = $logPath; mode = "hosted-wm-capture-evidence" }
    }
    if (-not (Test-Path -LiteralPath $entryPath)) {
        "missing hosted WM capture entry: $entryPath" | Set-Content -Encoding ASCII -Path $logPath
        return @{ attempted = "true"; status = "blocked:missing-host-capture-entry"; exit_code = ""; log_path = $logPath; mode = "hosted-wm-capture-evidence" }
    }
    $oldSimpleLib = $env:SIMPLE_LIB
    $oldCapturePath = $env:SIMPLE_HOSTED_WM_CAPTURE_PPM
    $oldStdoutPpm = $env:SIMPLE_HOSTED_WM_CAPTURE_STDOUT_PPM
    try {
        $env:SIMPLE_LIB = "src"
        $env:SIMPLE_HOSTED_WM_CAPTURE_PPM = $capturePath
        $env:SIMPLE_HOSTED_WM_CAPTURE_STDOUT_PPM = "1"
        $psi = [System.Diagnostics.ProcessStartInfo]::new()
        $psi.FileName = (Resolve-Path -LiteralPath $simpleBinary).Path
        $psi.Arguments = "`"$entryPath`" --interpret"
        $psi.WorkingDirectory = $repoRoot
        $psi.UseShellExecute = $false
        $psi.RedirectStandardOutput = $true
        $psi.RedirectStandardError = $true
        $psi.EnvironmentVariables["SIMPLE_LIB"] = "src"
        $psi.EnvironmentVariables["SIMPLE_HOSTED_WM_CAPTURE_PPM"] = $capturePath
        $psi.EnvironmentVariables["SIMPLE_HOSTED_WM_CAPTURE_STDOUT_PPM"] = "1"
        $proc = [System.Diagnostics.Process]::new()
        $proc.StartInfo = $psi
        $null = $proc.Start()
        $completed = $proc.WaitForExit($HostCaptureTimeoutSeconds * 1000)
        if (-not $completed) {
            try {
                $proc.Kill()
            } catch {
            }
            $stdout = $proc.StandardOutput.ReadToEnd()
            $stderr = $proc.StandardError.ReadToEnd()
            @(
                $stdout,
                $stderr,
                "hosted WM capture timed out",
                "timeout_seconds=$HostCaptureTimeoutSeconds",
                "simple_binary=$simpleBinary",
                "entry_path=$entryPath",
                "capture_path=$capturePath"
            ) | Where-Object { $_ -ne "" } | Set-Content -Encoding ASCII -Path $logPath
            return @{ attempted = "true"; status = "blocked:host-capture-timeout-${HostCaptureTimeoutSeconds}s"; exit_code = "timeout"; log_path = $logPath; mode = "hosted-wm-capture-stdout-ppm" }
        }
        $stdout = $proc.StandardOutput.ReadToEnd()
        $stderr = $proc.StandardError.ReadToEnd()
        $wroteStdoutPpm = Write-StdoutPpmCapture $stdout $capturePath
        @($stdout, $stderr) | Where-Object { $_ -ne "" } | Set-Content -Encoding ASCII -Path $logPath
        $exitCode = $proc.ExitCode
    } finally {
        $env:SIMPLE_LIB = $oldSimpleLib
        $env:SIMPLE_HOSTED_WM_CAPTURE_PPM = $oldCapturePath
        $env:SIMPLE_HOSTED_WM_CAPTURE_STDOUT_PPM = $oldStdoutPpm
    }
    if (-not (Test-FileNonEmpty $logPath)) {
        @(
            "hosted WM capture produced no stdout/stderr",
            "simple_binary=$simpleBinary",
            "entry_path=$entryPath",
            "capture_path=$capturePath",
            "exit_code=$exitCode"
        ) | Set-Content -Encoding ASCII -Path $logPath
    }
    $exitText = if ($exitCode -lt 0) { "neg$([Math]::Abs($exitCode))" } else { "$exitCode" }
    $status = if ($exitCode -eq 0 -and (Test-FileNonEmpty $capturePath)) { "pass" } else { "blocked:host-capture-exit-$exitText" }
    return @{ attempted = "true"; status = $status; exit_code = "$exitCode"; log_path = $logPath; mode = "hosted-wm-capture-stdout-ppm" }
}

$rows = [System.Collections.Generic.List[string]]::new()
if (-not [string]::IsNullOrWhiteSpace($BaseEvidencePath) -and (Test-Path -LiteralPath $BaseEvidencePath)) {
    Get-Content -LiteralPath $BaseEvidencePath | ForEach-Object {
        if (-not [string]::IsNullOrWhiteSpace($_)) {
            $rows.Add($_) | Out-Null
        }
    }
}

$hostCaptureAttempt = @{ attempted = "false"; status = "not-requested"; exit_code = ""; log_path = $HostCaptureLogPath; mode = "file-input" }
if ($AttemptHostWmCapture) {
    $hostCaptureAttempt = Invoke-HostWmCapture $SimpleBinary $HostCaptureEntry $HostPpmPath $HostCaptureLogPath
}

$qemu = Read-Ppm $QemuPpmPath
$hostCapture = Read-Ppm $HostPpmPath
$mismatchCount = Count-Mismatches $qemu $hostCapture
$qemuCaptureKind = Get-CaptureKind $qemu "qemu"
$hostCaptureKind = Get-CaptureKind $hostCapture "host"
$argbReason = Get-ArgbDiffReason $qemu $hostCapture $mismatchCount $qemuCaptureKind $hostCaptureKind
$argbStatus = if ($qemu.status -eq "pass" -and $hostCapture.status -eq "pass" -and $mismatchCount -eq 0) { "pass" } else { "blocked" }
$qemuWmSceneReady = ($qemu.status -eq "pass" -and $qemuCaptureKind -ne "qemu-virtio-gpu-test-pattern")
$hostWmSceneReady = ($hostCapture.status -eq "pass" -and $hostCaptureKind -ne "hosted-wm-diagnostic-crop")
$logCompare = Compare-RenderdocLogs $QemuRenderdocLogPath $HostRenderdocLogPath $WmSceneName
$logCompareStatus = $logCompare.status
$rdcMagic = Read-RdcMagic $SimpleRdcPath
$captureLogStatus = if (Test-FileNonEmpty $CaptureLogPath) { "pass" } else { "missing" }
$qemuWmStatus = if ($qemuWmSceneReady) { "pass" } else { "missing" }
$hostWmStatus = if ($hostWmSceneReady) { "pass" } else { "missing" }
$compareStatus = if ($argbStatus -eq "pass" -and $logCompareStatus -eq "pass") { "pass" } else { "missing" }

$evidenceDir = Split-Path -Parent $EvidencePath
if (-not [string]::IsNullOrWhiteSpace($evidenceDir)) {
    New-Item -ItemType Directory -Force -Path $evidenceDir | Out-Null
}

Write-Row $rows "simpleos_wm_host_compare_wrapper" "check-simpleos-wm-host-compare-evidence.ps1"
Write-Row $rows "simpleos_wm_qemu_ppm_path" "$QemuPpmPath"
Write-Row $rows "simpleos_wm_qemu_ppm_status" "$($qemu.status)"
Write-Row $rows "simpleos_wm_qemu_ppm_reason" "$($qemu.reason)"
Write-Row $rows "simpleos_wm_qemu_ppm_width" "$($qemu.width)"
Write-Row $rows "simpleos_wm_qemu_ppm_height" "$($qemu.height)"
Write-Row $rows "simpleos_wm_qemu_capture_kind" "$qemuCaptureKind"
Write-Row $rows "simpleos_wm_host_ppm_path" "$HostPpmPath"
Write-Row $rows "simpleos_wm_host_ppm_status" "$($hostCapture.status)"
Write-Row $rows "simpleos_wm_host_ppm_reason" "$($hostCapture.reason)"
Write-Row $rows "simpleos_wm_host_ppm_width" "$($hostCapture.width)"
Write-Row $rows "simpleos_wm_host_ppm_height" "$($hostCapture.height)"
Write-Row $rows "simpleos_wm_host_capture_kind" "$hostCaptureKind"
Write-Row $rows "simpleos_host_wm_capture_attempted" "$($hostCaptureAttempt.attempted)"
Write-Row $rows "simpleos_host_wm_capture_mode" "$($hostCaptureAttempt.mode)"
Write-Row $rows "simpleos_host_wm_capture_status" "$($hostCaptureAttempt.status)"
Write-Row $rows "simpleos_host_wm_capture_exit_code" "$($hostCaptureAttempt.exit_code)"
Write-Row $rows "simpleos_host_wm_capture_log_path" "$($hostCaptureAttempt.log_path)"
Write-Row $rows "simpleos_wm_compare_scene" "$WmSceneName"
Write-Row $rows "simpleos_wm_renderdoc_scene" "$RenderdocSceneName"
Write-Row $rows "simpleos_wm_qemu_scene" $(if ($qemuWmSceneReady) { $WmSceneName } else { "" })
Write-Row $rows "simpleos_wm_host_scene" $(if ($hostWmSceneReady) { $WmSceneName } else { "" })
Write-Row $rows "simpleos_wm_qemu_window_count" $(if ($qemuWmSceneReady) { "$WindowCount" } else { "0" })
Write-Row $rows "simpleos_wm_host_window_count" $(if ($hostWmSceneReady) { "$WindowCount" } else { "0" })
Write-Row $rows "simpleos_wm_qemu_focus_id" $(if ($qemuWmSceneReady) { $FocusId } else { "" })
Write-Row $rows "simpleos_wm_host_focus_id" $(if ($hostWmSceneReady) { $FocusId } else { "" })
Write-Row $rows "simpleos_wm_qemu_titlebar_status" $(if ($qemuWmSceneReady) { "pass" } else { "missing" })
Write-Row $rows "simpleos_wm_host_titlebar_status" $(if ($hostWmSceneReady) { "pass" } else { "missing" })
Write-Row $rows "simpleos_wm_qemu_taskbar_status" $(if ($qemuWmSceneReady) { "pass" } else { "missing" })
Write-Row $rows "simpleos_wm_host_taskbar_status" $(if ($hostWmSceneReady) { "pass" } else { "missing" })
Write-Row $rows "simpleos_wm_renderdoc_log_compare_status" "$logCompareStatus"
Write-Row $rows "simpleos_wm_renderdoc_log_compare_reason" "$($logCompare.reason)"
Write-Row $rows "simpleos_wm_renderdoc_log_compare_mode" "$($logCompare.mode)"
Write-Row $rows "simpleos_wm_renderdoc_qemu_log_status" "$($logCompare.qemu.status)"
Write-Row $rows "simpleos_wm_renderdoc_host_log_status" "$($logCompare.host.status)"
Write-Row $rows "simpleos_wm_renderdoc_qemu_log_scene" "$($logCompare.qemu.scene)"
Write-Row $rows "simpleos_wm_renderdoc_host_log_scene" "$($logCompare.host.scene)"
Write-Row $rows "simpleos_wm_renderdoc_qemu_log_backend" "$($logCompare.qemu.backend)"
Write-Row $rows "simpleos_wm_renderdoc_host_log_backend" "$($logCompare.host.backend)"
Write-Row $rows "simpleos_wm_argb_diff_status" "$argbStatus"
Write-Row $rows "simpleos_wm_argb_diff_reason" "$argbReason"
Write-Row $rows "simpleos_wm_argb_mismatch_count" "$mismatchCount"
Write-Row $rows "simpleos_wm_qemu_host_compare_status" "$compareStatus"

Write-Row $rows "simpleos_renderdoc_capture_mode" "capture-simple"
Write-Row $rows "simpleos_renderdoc_rdc_path" "$SimpleRdcPath"
Write-Row $rows "simpleos_renderdoc_rdc_magic" "$rdcMagic"
Write-Row $rows "simpleos_renderdoc_rdc_magic_status" $(if ($rdcMagic -eq "RDOC") { "pass" } else { "missing" })
Write-Row $rows "simpleos_renderdoc_rdc_status" $(if ($rdcMagic -eq "RDOC") { "pass" } else { "missing" })
Write-Row $rows "simpleos_renderdoc_rdc_size_bytes" (Get-FileSizeText $SimpleRdcPath)
Write-Row $rows "simpleos_renderdoc_capture_log_path" "$CaptureLogPath"
Write-Row $rows "simpleos_renderdoc_capture_log_status" "$captureLogStatus"
Write-Row $rows "simpleos_renderdoc_simple_runtime_backend" $(if ($rdcMagic -eq "RDOC") { "vulkan" } else { "missing" })
Write-Row $rows "simpleos_renderdoc_simple_scene" $(if ($rdcMagic -eq "RDOC") { $RenderdocSceneName } else { "" })
Write-Row $rows "simpleos_renderdoc_helper_status" "$captureLogStatus"
Write-Row $rows "simpleos_renderdoc_qemu_wm_log_path" $(if (Test-FileNonEmpty $QemuRenderdocLogPath) { $QemuRenderdocLogPath } else { "" })
Write-Row $rows "simpleos_renderdoc_host_wm_log_path" $(if (Test-FileNonEmpty $HostRenderdocLogPath) { $HostRenderdocLogPath } else { "" })

Write-Row $rows "simpleos_simple2d_readback_status" $(if ($qemu.status -eq "pass") { "pass" } else { "missing" })
Write-Row $rows "simpleos_qemu_gpu_readback_status" $(if ($qemu.status -eq "pass") { "pass" } else { "missing" })
Write-Row $rows "simpleos_qemu_wm_evidence_status" "$qemuWmStatus"
Write-Row $rows "simpleos_host_wm_evidence_status" "$hostWmStatus"

$rows | Set-Content -Encoding ASCII -Path $EvidencePath
$rows | ForEach-Object { Write-Output $_ }
Write-Output "simpleos_wm_host_compare_evidence_path=$EvidencePath"

if ($compareStatus -eq "pass" -and $rdcMagic -eq "RDOC" -and $captureLogStatus -eq "pass") {
    exit 0
}
exit 1
