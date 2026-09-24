param(
    [string]$Candidate,
    [Parameter(Mandatory = $true)][string]$Destination,
    [string]$ExpectedSha256,
    [string]$Receipt,
    [string]$Backup,
    [switch]$Restore
)

$ErrorActionPreference = 'Stop'

function Get-Sha256([string]$Path) {
    $stream = [IO.File]::OpenRead($Path)
    try {
        $sha = [Security.Cryptography.SHA256]::Create()
        try { -join ($sha.ComputeHash($stream) | ForEach-Object { $_.ToString('x2') }) }
        finally { $sha.Dispose() }
    } finally { $stream.Dispose() }
}

function Require-PlainFile([string]$Path, [string]$Name) {
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "$Name is missing: $Path"
    }
    $item = Get-Item -Force -LiteralPath $Path
    if ($item.Attributes -band [IO.FileAttributes]::ReparsePoint) {
        throw "$Name must not be a reparse point: $Path"
    }
}

if ($Restore) {
    # Copy the durable backup: recovery must remain repeatable after a crash.
    $Candidate = $Backup
}

$expected = $ExpectedSha256.ToLowerInvariant()
if ($expected -notmatch '^[0-9a-f]{64}$') { throw 'ExpectedSha256 must be a lowercase SHA-256 digest' }
Require-PlainFile $Candidate 'candidate'

$candidateHash = Get-Sha256 $Candidate
if ($candidateHash -ne $expected) { throw "candidate SHA-256 differs from admitted digest: $Candidate" }

$destinationDirectory = Split-Path -Parent $Destination
if (-not (Test-Path -LiteralPath $destinationDirectory -PathType Container)) {
    throw "destination directory is missing: $destinationDirectory"
}
if (Test-Path -LiteralPath $Destination -PathType Container) { throw "destination is a directory: $Destination" }
if (Test-Path -LiteralPath $Destination) { Require-PlainFile $Destination 'destination' }

# The staged file is deliberately in the destination directory: File.Replace and
# File.Move are then same-volume operations. A failure before replacement leaves
# the running stable executable untouched.
$stage = Join-Path $destinationDirectory ('.simple.exe.stage.' + [Guid]::NewGuid().ToString('N'))
$backupPath = if ([string]::IsNullOrWhiteSpace($Backup)) { Join-Path $destinationDirectory ('.simple.exe.backup.' + [Guid]::NewGuid().ToString('N')) } else { $Backup }
[IO.Path]::GetFullPath($backupPath) | Out-Null
$keepBackup = (-not $Restore) -and (-not [string]::IsNullOrWhiteSpace($Backup))
if ($Restore) { $backupPath = "$Destination.restore-discard.$([Guid]::NewGuid().ToString('N'))" }
$receiptStage = "$Receipt.stage.$([Guid]::NewGuid().ToString('N'))"
$receiptDiscard = "$Receipt.discard.$([Guid]::NewGuid().ToString('N'))"
$failureDiscard = "$Destination.failure-discard.$([Guid]::NewGuid().ToString('N'))"
$published = $false
$existed = Test-Path -LiteralPath $Destination
try {
    Copy-Item -LiteralPath $Candidate -Destination $stage -ErrorAction Stop
    if ((Get-Sha256 $stage) -ne $expected) { throw 'staged candidate SHA-256 mismatch' }

    if (Test-Path -LiteralPath $Destination) {
        # Replace is atomic and refuses a locked destination; it never degrades
        # into truncate-and-copy, which is the stale/partial binary failure mode.
        if ($keepBackup -and (Test-Path -LiteralPath $backupPath)) { throw 'backup already exists' }
        [IO.File]::Replace($stage, $Destination, $backupPath)
    } else {
        [IO.File]::Move($stage, $Destination)
    }
    $published = $true
    if ((Get-Sha256 $Destination) -ne $expected) { throw 'stable executable SHA-256 mismatch after replacement' }

    if ($Restore) {
        Write-Output "WINDOWS_STABLE_ENTRYPOINT_RESTORED stable_path=$Destination"
        return
    }

    $candidateStamp = (Get-Item -LiteralPath $Candidate).LastWriteTimeUtc.ToString('o')
    $deployedStamp = (Get-Item -LiteralPath $Destination).LastWriteTimeUtc.ToString('o')
    @(
        'schema=simple-windows-stable-entrypoint-receipt-v1'
        'status=pass'
        "candidate_path=$Candidate"
        "candidate_sha256=$candidateHash"
        "candidate_last_write_utc=$candidateStamp"
        "stable_path=$Destination"
        "stable_sha256=$expected"
        "stable_last_write_utc=$deployedStamp"
    ) | Set-Content -LiteralPath $receiptStage -NoNewline:$false -Encoding ascii
    if (Test-Path -LiteralPath $Receipt) {
        Require-PlainFile $Receipt 'receipt'
        [IO.File]::Replace($receiptStage, $Receipt, $receiptDiscard)
    } else {
        [IO.File]::Move($receiptStage, $Receipt)
    }
    Write-Output "WINDOWS_STABLE_ENTRYPOINT_PUBLISHED candidate_sha256=$candidateHash stable_sha256=$expected receipt=$Receipt"
} catch {
    if ($published -and (-not $Restore)) {
        # If rollback itself is blocked, retain the only local original copy.
        $keepBackup = $true
        if ($existed) { [IO.File]::Replace($backupPath, $Destination, $failureDiscard) }
        else { Remove-Item -LiteralPath $Destination -Force }
    }
    throw
} finally {
    if (Test-Path -LiteralPath $stage) { Remove-Item -LiteralPath $stage -Force -ErrorAction SilentlyContinue }
    if ((-not $keepBackup) -and (Test-Path -LiteralPath $backupPath)) { Remove-Item -LiteralPath $backupPath -Force -ErrorAction SilentlyContinue }
    if (Test-Path -LiteralPath $receiptStage) { Remove-Item -LiteralPath $receiptStage -Force -ErrorAction SilentlyContinue }
    if (Test-Path -LiteralPath $receiptDiscard) { Remove-Item -LiteralPath $receiptDiscard -Force -ErrorAction SilentlyContinue }
    if (Test-Path -LiteralPath $failureDiscard) { Remove-Item -LiteralPath $failureDiscard -Force -ErrorAction SilentlyContinue }
}
