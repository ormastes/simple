# Link binaries from bin/rust/ to bin/simple/ for Windows

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProjectRoot = Split-Path -Parent $ScriptDir
$BinRust = Join-Path $ProjectRoot "bin\rust"
$BinSimple = Join-Path $ProjectRoot "bin\simple"

Write-Host "Creating binary symlinks..." -ForegroundColor Cyan

# Create bin/simple directory if it doesn't exist
New-Item -ItemType Directory -Force -Path $BinSimple | Out-Null

# Define binaries to link (add .exe extension on Windows)
$Binaries = @(
    "simple.exe",
    "simple-fmt.exe",
    "simple-lint.exe",
    "simple-test.exe",
    "smh_coverage.exe"
)

# Create symlinks (requires admin or developer mode)
foreach ($binary in $Binaries) {
    $source = Join-Path $BinRust $binary
    $target = Join-Path $BinSimple $binary

    if (Test-Path $source) {
        Write-Host "  Linking $binary..." -ForegroundColor Gray

        # Remove existing symlink if present
        if (Test-Path $target) {
            Remove-Item $target -Force
        }

        # Create symlink (requires admin or Windows Developer Mode)
        New-Item -ItemType SymbolicLink -Path $target -Target $source | Out-Null
    } else {
        Write-Host "  Warning: $source not found, skipping" -ForegroundColor Yellow
    }
}

Write-Host "✅ Binary links created in $BinSimple" -ForegroundColor Green
Write-Host ""
Write-Host "Add to your PATH:" -ForegroundColor Cyan
Write-Host "  `$env:PATH = `"$BinSimple;`$env:PATH`"" -ForegroundColor White
