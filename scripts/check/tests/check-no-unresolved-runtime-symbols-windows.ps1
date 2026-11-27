param(
    [Parameter(Mandatory=$true)][string]$EvidenceDir,
    [ValidateSet('Prepare','Check','CheckExtra','All')][string]$Phase = 'All',
    [string]$LlvmBin = 'C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin',
    [string]$Bash = 'C:/dev/tool/Git/bin/bash.exe'
)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path "$PSScriptRoot/../../..").Path.Replace('\','/')
$utf8 = New-Object System.Text.UTF8Encoding($false)
function Write-Utf8([string]$Path, [string]$Value) { [IO.File]::WriteAllText($Path,$Value,$utf8) }
function Invoke-Checked([string]$Exe,[string[]]$Arguments,[string]$Log) {
    $ErrorActionPreference = 'Continue'
    $output = @(& $Exe @Arguments 2>&1)
    $code = $LASTEXITCODE
    Write-Utf8 $Log (($output | ForEach-Object { "$_" }) -join "`n")
    if ($code -ne 0) { throw "$Exe exited $code; see $Log" }
}
if ($Phase -eq 'Prepare' -or $Phase -eq 'All') {
    if (Test-Path -LiteralPath $EvidenceDir) { throw 'Prepare requires a fresh private evidence directory.' }
    New-Item -ItemType Directory -Path $EvidenceDir | Out-Null
    foreach ($name in @('good','bad','missing','ordinal','forward')) {
        New-Item -ItemType Directory -Path "$EvidenceDir/$name" | Out-Null
    }
    $entry = 'int DllMainCRTStartup(void *h, unsigned long reason, void *reserved) { return 1; }'
    Write-Utf8 "$EvidenceDir/good.c" ('__declspec(dllexport) int rt_fixture(void) { return 42; } ' + $entry)
    Write-Utf8 "$EvidenceDir/bad.c" ('__declspec(dllexport) int unrelated_fixture(void) { return 42; } ' + $entry)
    Write-Utf8 "$EvidenceDir/client.c" '__declspec(dllimport) int rt_fixture(void); int fixture_entry(void) { return rt_fixture() - 42; }'
    $dllArgs = @('--target=x86_64-w64-windows-gnu','-fuse-ld=lld','-nostdlib','-O0','-g','-shared','-Wl,--entry,DllMainCRTStartup')
    Invoke-Checked "$LlvmBin/clang.exe" ($dllArgs + @("$EvidenceDir/good.c","-Wl,--out-implib,$EvidenceDir/good/owner.lib",'-o',"$EvidenceDir/good/owner.dll")) "$EvidenceDir/compile-good-dll.log"
    Invoke-Checked "$LlvmBin/clang.exe" ($dllArgs + @("$EvidenceDir/bad.c",'-o',"$EvidenceDir/bad/owner.dll")) "$EvidenceDir/compile-bad-dll.log"
    Copy-Item -LiteralPath "$EvidenceDir/good/owner.dll" -Destination "$EvidenceDir/bad/unrelated.dll"
    $exeArgs = @('--target=x86_64-w64-windows-gnu','-fuse-ld=lld','-nostdlib','-O0','-g',"$EvidenceDir/client.c",'-Wl,--entry,fixture_entry','-Wl,--subsystem,console')
    Invoke-Checked "$LlvmBin/clang.exe" ($exeArgs + @("$EvidenceDir/good/owner.lib",'-o',"$EvidenceDir/good/client.exe")) "$EvidenceDir/compile-client.log"
    foreach ($name in @('bad','missing')) { Copy-Item -LiteralPath "$EvidenceDir/good/client.exe" -Destination "$EvidenceDir/$name/client.exe" }
    Invoke-Checked "$LlvmBin/llvm-strip.exe" @('--strip-all',"$EvidenceDir/good/client.exe",'-o',"$EvidenceDir/good/stripped.exe") "$EvidenceDir/strip.log"
    Write-Utf8 "$EvidenceDir/ordinal.def" "LIBRARY owner.dll`nEXPORTS`n  rt_fixture @7 NONAME`n"
    Invoke-Checked "$LlvmBin/clang.exe" ($dllArgs + @("$EvidenceDir/good.c","$EvidenceDir/ordinal.def","-Wl,--out-implib,$EvidenceDir/ordinal/owner.lib",'-o',"$EvidenceDir/ordinal/owner.dll")) "$EvidenceDir/compile-ordinal-dll.log"
    Invoke-Checked "$LlvmBin/clang.exe" ($exeArgs + @("$EvidenceDir/ordinal/owner.lib",'-o',"$EvidenceDir/ordinal/client.exe")) "$EvidenceDir/compile-ordinal-client.log"
    Write-Utf8 "$EvidenceDir/forward.def" "LIBRARY owner.dll`nEXPORTS`n  rt_fixture=other.rt_fixture`n"
    Invoke-Checked "$LlvmBin/clang.exe" ($dllArgs + @("$EvidenceDir/bad.c","$EvidenceDir/forward.def",'-o',"$EvidenceDir/forward/owner.dll")) "$EvidenceDir/compile-forward-dll.log"
    Copy-Item -LiteralPath "$EvidenceDir/good/client.exe" -Destination "$EvidenceDir/forward/client.exe"
    Invoke-Checked "$EvidenceDir/good/client.exe" @() "$EvidenceDir/native-good.log"
    $receipt = @('status native_fixture_good_execution_only','good_native_exit_code 0','broken_candidates_executed false','simple_compiler_executed false',"source_base $(git -C $repo rev-parse HEAD)")
    foreach ($path in @("$LlvmBin/clang.exe","$LlvmBin/llvm-nm.exe","$LlvmBin/llvm-readobj.exe","$LlvmBin/llvm-strip.exe","$EvidenceDir/good/client.exe","$EvidenceDir/good/owner.dll","$EvidenceDir/bad/owner.dll","$EvidenceDir/ordinal/client.exe","$EvidenceDir/forward/owner.dll")) {
        $receipt += "artifact { path `"$($path.Replace('\','/'))`" sha256 $((Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLower()) }"
    }
    Write-Utf8 "$EvidenceDir/native-fixtures.sdn" (($receipt -join "`n")+"`n")
    Write-Output "Native good owner/import fixture returned zero: $EvidenceDir/native-fixtures.sdn"
    if ($Phase -eq 'Prepare') { exit 0 }
}
if (!(Test-Path -LiteralPath "$EvidenceDir/native-fixtures.sdn")) { throw 'Prepare native evidence first.' }
$checks = @'
set -eu
repo=$1 tools=$2 evidence=$3
export NM="$tools/llvm-nm.exe" PE_READOBJ="$tools/llvm-readobj.exe"
guard="$repo/scripts/check/check-no-unresolved-runtime-symbols.shs"
expect_result() {
  label=$1 expected=$2 binary=$3 pattern=$4
  set +e
  sh "$guard" --bin "$binary" > "$evidence/$label.log" 2>&1
  result=$?
  set -e
  test "$result" -eq "$expected" || { echo "$label: unexpected exit $result" >&2; cat "$evidence/$label.log" >&2; exit 1; }
  grep -q "$pattern" "$evidence/$label.log"
}
case "${4:-all}" in all|base)
expect_result good 0 "$evidence/good/client.exe" '^PASS'
expect_result wrong-owner 1 "$evidence/bad/client.exe" 'owner.dll:rt_fixture'
expect_result missing-owner 2 "$evidence/missing/client.exe" '^ERROR'
expect_result stripped 2 "$evidence/good/stripped.exe" '^ERROR'
expect_result ordinal 2 "$evidence/ordinal/client.exe" 'ordinal'
expect_result forward 2 "$evidence/forward/client.exe" 'forward'
cat > "$evidence/failed-reader.sh" <<'TOOL'
#!/bin/sh
"$REAL_READOBJ" "$@"
exit 7
TOOL
chmod +x "$evidence/failed-reader.sh"
export REAL_READOBJ="$PE_READOBJ"
PE_READOBJ="$evidence/failed-reader.sh"
expect_result partial-reader 2 "$evidence/good/client.exe" '^ERROR'
;; esac
case "${4:-all}" in all|extra)
export REAL_READOBJ="$tools/llvm-readobj.exe"
cat > "$evidence/altered-reader.sh" <<'TOOL'
#!/bin/sh
"$REAL_READOBJ" "$@" > "$ALTERED_OUTPUT"
status=$?
test "$status" -eq 0 || exit "$status"
case "$ALTER_MODE" in
 delay) sed 's/DelayImportDescriptorRVA: 0x0/DelayImportDescriptorRVA: 0x1/' "$ALTERED_OUTPUT";;
 machine) sed 's/IMAGE_FILE_MACHINE_AMD64 (0x8664)/IMAGE_FILE_MACHINE_ARM64 (0xAA64)/' "$ALTERED_OUTPUT";;
 pointer) sed '/PointerToSymbolTable:/d' "$ALTERED_OUTPUT";;
 truncated-import) cat "$ALTERED_OUTPUT"; printf 'Import {\n  Name: hidden.dll\n  Symbol: rt_hidden (0)\n';;
 truncated-export)
   cat "$ALTERED_OUTPUT"
   case " $* " in *' --coff-exports '*) printf 'Export {\n  Name: rt_hidden\n';; esac;;
esac
TOOL
chmod +x "$evidence/altered-reader.sh"
export ALTERED_OUTPUT="$evidence/altered-reader-source.txt"
PE_READOBJ="$evidence/altered-reader.sh"
export ALTER_MODE=delay
expect_result delay-coverage 2 "$evidence/good/client.exe" 'delay imports'
ALTER_MODE=machine
expect_result unsupported-machine 2 "$evidence/good/client.exe" 'unsupported PE machine'
ALTER_MODE=pointer
expect_result incomplete-header 2 "$evidence/good/client.exe" 'PointerToSymbolTable'
ALTER_MODE=truncated-import
expect_result truncated-import 2 "$evidence/good/client.exe" 'incomplete PE import block'
ALTER_MODE=truncated-export
expect_result truncated-export 2 "$evidence/good/client.exe" 'incomplete PE export block'
PE_READOBJ="$REAL_READOBJ"
mkdir -p "$evidence/application with spaces"
cp "$evidence/good/client.exe" "$evidence/application with spaces/client.exe"
cp "$evidence/good/owner.dll" "$evidence/application with spaces/owner.dll"
expect_result spaces 0 "$evidence/application with spaces/client.exe" '^PASS'
cat > "$evidence/undefined-nm.sh" <<'TOOL'
#!/bin/sh
if [ "$1" = -u ]; then printf '         U %s\n' "$UNDEFINED_NAME"; else "$REAL_NM" "$@"; fi
TOOL
chmod +x "$evidence/undefined-nm.sh"
export REAL_NM="$NM"
NM="$evidence/undefined-nm.sh"
export UNDEFINED_NAME=rt_unmapped
expect_result undefined-runtime 1 "$evidence/good/client.exe" 'COFF:rt_unmapped'
UNDEFINED_NAME=rt_fixture
expect_result undefined-same-import 1 "$evidence/good/client.exe" 'COFF:rt_fixture'
UNDEFINED_NAME=__imp_rt_unmapped
expect_result unmapped-import-pointer 1 "$evidence/good/client.exe" 'COFF:__imp_rt_unmapped'
UNDEFINED_NAME=__imp_rt_fixture
expect_result mapped-import-pointer 0 "$evidence/good/client.exe" '^PASS'
set +e
PE_READOBJ=nonexistent-pe-reader sh "$guard" --archive-only --root "$evidence/missing" > "$evidence/archive-no-pe-reader.log" 2>&1
archive_result=$?
sh "$guard" --selftest-only --bin "$evidence/good/client.exe" > "$evidence/selftest-conflict.log" 2>&1
selftest_result=$?
set -e
test "$archive_result" -eq 2
grep -q '0 artifacts inspected' "$evidence/archive-no-pe-reader.log"
test "$selftest_result" -eq 2
grep -q 'selftest-only requires its own fixture dispatch' "$evidence/selftest-conflict.log"
;; esac
echo 'PASS Windows x64 COFF and named-runtime-import owner fixtures; no compiler qualification'
'@
$checkName = if ($Phase -eq 'CheckExtra') { 'check-extra' } else { 'check' }
$group = if ($Phase -eq 'CheckExtra') { 'extra' } else { 'all' }
Write-Utf8 "$EvidenceDir/$checkName.sh" ($checks.Replace("`r",'')+"`n")
Invoke-Checked $Bash @("$EvidenceDir/$checkName.sh",$repo,$LlvmBin,$EvidenceDir,$group) "$EvidenceDir/$checkName.log"
Get-Content -LiteralPath "$EvidenceDir/$checkName.log"
