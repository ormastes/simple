[CmdletBinding()]
param(
    [switch]$Dump,
    [ValidateSet("producer","matrix")][string]$Consumer = "producer",
    [string]$PolicyPath = (Join-Path $PSScriptRoot "sosix-qemu-compiler-designation-v1.tsv")
)

function Read-SosixQemuCompilerDesignationPolicy([string]$Path) {
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { throw "missing compiler designation policy:$Path" }
    $hosts=@("linux","windows","macos","freebsd")
    $guests=@("x86_32","x86_64","arm32","arm64","riscv32","riscv64")
    $policy=@{}
    foreach ($line in [System.IO.File]::ReadAllLines((Resolve-Path -LiteralPath $Path).Path)) {
        $parts=$line.Split('|')
        if ($parts.Count -ne 3 -or $parts[0] -notin $hosts -or $parts[1] -notin $guests -or $parts[2] -notin @("true","false")) { throw "malformed compiler designation policy" }
        $key="$($parts[0])|$($parts[1])"
        if ($policy.ContainsKey($key)) { throw "duplicate compiler designation policy cell:$key" }
        $policy[$key]=$parts[2]
    }
    if ($policy.Count -ne 24) { throw "compiler designation policy must contain 24 cells" }
    foreach ($hostKey in $hosts) { foreach ($guestKey in $guests) {
        if (-not $policy.ContainsKey("$hostKey|$guestKey")) { throw "missing compiler designation policy cell:$hostKey|$guestKey" }
    } }
    return $policy
}

function Write-SosixQemuCompilerDesignationPolicy([string]$Path) {
    $policy=Read-SosixQemuCompilerDesignationPolicy $Path
    foreach ($key in @($policy.Keys | Sort-Object)) { Write-Output "$key|$($policy[$key])" }
}

if ($Dump) {
    try { Write-SosixQemuCompilerDesignationPolicy $PolicyPath }
    catch { [Console]::Error.WriteLine($_.Exception.Message); exit 2 }
}
