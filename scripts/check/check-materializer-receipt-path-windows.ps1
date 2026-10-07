param(
    [string]$SourcePath = (Join-Path $PSScriptRoot '../setup/materialize-symlinks-windows.shs'),
    [string]$BashPath = (Join-Path $env:ProgramFiles 'Git/bin/bash.exe')
)
$ErrorActionPreference = 'Stop'
$source = [IO.File]::ReadAllText((Resolve-Path -LiteralPath $SourcePath))
$functions = [regex]::Matches($source, '(?ms)^receipt_to_win_path\(\) \{\r?\n.*?^\}')
if ($functions.Count -ne 1) { throw 'expected exactly one receipt path implementation' }
if (!(Test-Path -LiteralPath $BashPath -PathType Leaf)) { throw 'Git Bash is required' }
$fixture = Join-Path $env:TEMP ('materializer-receipt-test-' + [guid]::NewGuid().ToString('N'))
[IO.Directory]::CreateDirectory($fixture) | Out-Null
try {
    $checks = @'
checks=0
expect_reject() {
    checks=$((checks + 1))
    if receipt_to_win_path "$1" >/dev/null; then
        printf 'FAIL: accepted reserved or invalid path: %s\n' "$1" >&2
        exit 1
    fi
}
expect_accept() {
    checks=$((checks + 1))
    actual=$(receipt_to_win_path "$1") || { printf 'FAIL: rejected valid path: %s\n' "$1" >&2; exit 1; }
    [ "$actual" = "$2" ] || { printf 'FAIL: changed lexical spelling: %s\n' "$1" >&2; exit 1; }
}
for prefix in COM com CoM LPT lpt LpT; do
    for digit in 1 2 3 4 5 6 7 8 9 ¹ ² ³; do
        expect_reject "/c/receipt/$prefix$digit"
        expect_reject "/c/receipt/$prefix$digit.txt"
        expect_reject "/c/receipt/$prefix$digit/child"
    done
done
for name in CON con CoN PRN prn PrN AUX aux AuX NUL nul NuL; do
    expect_reject "/c/receipt/$name"
    expect_reject "/c/receipt/$name.txt"
done
for path in /c/receipt/../escape /c/receipt//child /c/receipt/name. '/c/receipt/name ' /c/receipt/CON:stream; do
    expect_reject "$path"
done
expect_accept '/c/receipt/COM1x' 'C:\receipt\COM1x'
expect_accept '/c/receipt/COM¹x' 'C:\receipt\COM¹x'
expect_accept '/c/receipt/LPT²x' 'C:\receipt\LPT²x'
expect_accept '/c/receipt/CONsole' 'C:\receipt\CONsole'
expect_accept '/c/receipt/café' 'C:\receipt\café'
expect_accept '/c/receipt/한글' 'C:\receipt\한글'
expect_accept '/c/receipt/notes ¹' 'C:\receipt\notes ¹'
[ "$checks" -eq 252 ] || { printf 'FAIL: wrong case count %s\n' "$checks" >&2; exit 1; }
printf 'materializer receipt paths: PASS %s checks, LC_ALL=C\n' "$checks"
'@
    $script = Join-Path $fixture 'receipt-paths.shs'
    [IO.File]::WriteAllText($script, "#!/bin/bash`nexport LC_ALL=C`n" + $functions[0].Value + "`n" + $checks + "`n", [Text.UTF8Encoding]::new($false))
    & $BashPath --noprofile --norc $script
    if ($LASTEXITCODE -ne 0) { throw 'receipt path behavior regression' }
} finally {
    $tempRoot = [IO.Path]::GetFullPath($env:TEMP).TrimEnd('\') + '\'
    $fixturePath = [IO.Path]::GetFullPath($fixture)
    if (!$fixturePath.StartsWith($tempRoot, [StringComparison]::OrdinalIgnoreCase)) { throw 'unsafe fixture cleanup path' }
    Remove-Item -LiteralPath $fixturePath -Recurse -Force
}
