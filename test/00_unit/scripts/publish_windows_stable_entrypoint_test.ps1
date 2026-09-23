$ErrorActionPreference = 'Stop'
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$Publisher = Join-Path $Root 'scripts\bootstrap\publish-windows-stable-entrypoint.ps1'
$Work = Join-Path ([IO.Path]::GetTempPath()) ('simple windows deploy spaces ' + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory -Path $Work | Out-Null
function Get-Sha256([string]$Path) {
    $stream = [IO.File]::OpenRead($Path)
    try {
        $sha = [Security.Cryptography.SHA256]::Create()
        try { -join ($sha.ComputeHash($stream) | ForEach-Object { $_.ToString('x2') }) }
        finally { $sha.Dispose() }
    } finally { $stream.Dispose() }
}
try {
    $candidate = Join-Path $Work 'candidate.exe'
    $stable = Join-Path $Work 'simple.exe'
    $receipt = Join-Path $Work 'receipt.env'
    [IO.File]::WriteAllBytes($candidate, [byte[]](1,2,3,4))
    [IO.File]::WriteAllBytes($stable, [byte[]](9,9,9,9))
    $hash = Get-Sha256 $candidate

    & $Publisher -Candidate $candidate -Destination $stable -ExpectedSha256 $hash -Receipt $receipt
    if (-not $?) { throw 'publisher failed' }
    if ((Get-Sha256 $stable) -ne $hash) { throw 'stable bytes remain stale' }
    if (-not (Select-String -LiteralPath $receipt -SimpleMatch "stable_sha256=$hash" -Quiet)) { throw 'receipt lacks deployed hash' }

    # A deterministic rebuild can have identical bytes. It must still publish.
    & $Publisher -Candidate $candidate -Destination $stable -ExpectedSha256 $hash -Receipt $receipt
    if (-not $?) { throw 'unchanged-content rebuild was rejected' }

    $before = Get-Sha256 $stable
    $bad = '0' * 64
    $badRejected = $false
    try { & $Publisher -Candidate $candidate -Destination $stable -ExpectedSha256 $bad -Receipt $receipt } catch { $badRejected = $true }
    if (-not $badRejected) { throw 'bad digest unexpectedly published' }
    if ((Get-Sha256 $stable) -ne $before) { throw 'failed publish altered stable executable' }

    # A locked running executable must fail closed. The publisher may never
    # fall back to delete/truncate/copy when ReplaceFile cannot acquire it.
    $lockedBefore = Get-Sha256 $stable
    [IO.File]::WriteAllBytes($candidate, [byte[]](5,6,7,8))
    $lockedCandidate = Get-Sha256 $candidate
    $lock = [IO.File]::Open($stable, [IO.FileMode]::Open, [IO.FileAccess]::Read, [IO.FileShare]::None)
    try {
        $lockedRejected = $false
        try { & $Publisher -Candidate $candidate -Destination $stable -ExpectedSha256 $lockedCandidate -Receipt $receipt } catch { $lockedRejected = $true }
        if (-not $lockedRejected) { throw 'locked destination unexpectedly published' }
    } finally { $lock.Dispose() }
    if ((Get-Sha256 $stable) -ne $lockedBefore) { throw 'locked publish altered stable executable' }

    $receiptBefore = Get-Sha256 $receipt
    $receiptLock = [IO.File]::Open($receipt, [IO.FileMode]::Open, [IO.FileAccess]::Read, [IO.FileShare]::None)
    try {
        $receiptRejected = $false
        try { & $Publisher -Candidate $candidate -Destination $stable -ExpectedSha256 $lockedCandidate -Receipt $receipt } catch { $receiptRejected = $true }
        if (-not $receiptRejected) { throw 'locked receipt unexpectedly accepted' }
    } finally { $receiptLock.Dispose() }
    if ((Get-Sha256 $stable) -ne $lockedBefore) { throw 'receipt failure did not restore executable' }
    if ((Get-Sha256 $receipt) -ne $receiptBefore) { throw 'receipt failure changed prior receipt' }

    # Keep the fully qualified staging name below the legacy Windows 260-byte
    # limit while still exercising a deep path with spaces.
    $long = Join-Path $Work ('nested ' * 7)
    New-Item -ItemType Directory -Path $long -Force | Out-Null
    $longStable = Join-Path $long 'simple.exe'
    & $Publisher -Candidate $candidate -Destination $longStable -ExpectedSha256 $lockedCandidate -Receipt (Join-Path $long 'receipt.env')
    if ((Get-Sha256 $longStable) -ne $lockedCandidate) { throw 'long-path publish failed' }
    Write-Output 'PASS publish-windows-stable-entrypoint unchanged failed atomic spaces long-path'
} finally {
    if (Test-Path -LiteralPath $Work) { Remove-Item -LiteralPath $Work -Force -Recurse }
}
