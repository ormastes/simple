param(
    [Parameter(Mandatory=$true)][string]$EvidenceDir,
    [ValidateSet('Prepare','Check','CheckBounds')][string]$Phase = 'Check',
    [string]$LlvmBin = 'C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin',
    [string]$Bash = 'C:/dev/tool/Git/bin/bash.exe',
    [string]$UcrtLib = 'C:/Program Files (x86)/Windows Kits/10/Lib/10.0.26100.0/ucrt/x64/ucrt.lib'
)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path "$PSScriptRoot/../../..").Path
$utf8 = New-Object System.Text.UTF8Encoding($false)
function Write-Utf8([string]$Path, [string]$Value) { [IO.File]::WriteAllText($Path, $Value, $utf8) }
function Invoke-Checked([string]$Exe, [string[]]$Arguments, [string]$Log) {
    $output = @(& $Exe @Arguments 2>&1)
    $code = $LASTEXITCODE
    Write-Utf8 $Log (($output | ForEach-Object { "$_" }) -join "`n")
    if ($code -ne 0) { throw "$Exe exited $code; see $Log" }
}
if ($Phase -eq 'Prepare') {
    if (Test-Path -LiteralPath $EvidenceDir) { throw 'Prepare requires a new evidence directory.' }
    New-Item -ItemType Directory -Path $EvidenceDir | Out-Null
    $exports = 0..149 | ForEach-Object { "__declspec(dllexport) int rt_census_export_$_(void) { return $_; }" }
    $source = ($exports -join "`n") + "`nstatic int rt_census_private(void) { return 42; }`nint fixture_entry(void) { return rt_census_export_0() + rt_census_private() - 42; }`n"
    Write-Utf8 "$EvidenceDir/full.c" $source
    Invoke-Checked "$LlvmBin/clang.exe" @('--target=x86_64-w64-windows-gnu','-fuse-ld=lld','-nostdlib','-O0','-g',"$EvidenceDir/full.c",'-Wl,--entry,fixture_entry','-Wl,--subsystem,console','-Wl,--no-insert-timestamp','-o',"$EvidenceDir/full.exe") "$EvidenceDir/compile-full.log"
    Invoke-Checked "$LlvmBin/llvm-strip.exe" @('--strip-all',"$EvidenceDir/full.exe",'-o',"$EvidenceDir/stripped.exe") "$EvidenceDir/strip.log"
    $crtSource = '__declspec(dllimport) void *malloc(unsigned long long); __declspec(dllimport) void free(void *); int fixture_entry(void) { void *p = malloc(8); if (!p) return 1; free(p); return 0; }'
    Write-Utf8 "$EvidenceDir/crt.c" $crtSource
    Invoke-Checked "$LlvmBin/clang.exe" @('--target=x86_64-pc-windows-msvc','-fuse-ld=lld','-nostdlib','-O0',"$EvidenceDir/crt.c",$UcrtLib,'-Xlinker','/entry:fixture_entry','-Xlinker','/subsystem:console','-Xlinker','/nodefaultlib','-o',"$EvidenceDir/crt.exe") "$EvidenceDir/compile-crt.log"
    foreach ($name in @('full','stripped','crt')) {
        Invoke-Checked "$EvidenceDir/$name.exe" @() "$EvidenceDir/run-$name.log"
    }
    $receipt = @('status native_fixture_execution_only','simple_runtime_executed false',"source_head $(git -C $repo rev-parse HEAD)")
    foreach ($path in @("$LlvmBin/clang.exe","$LlvmBin/llvm-nm.exe","$LlvmBin/llvm-readobj.exe","$LlvmBin/llvm-strip.exe",$UcrtLib,"$env:SystemRoot/System32/ucrtbase.dll","$EvidenceDir/full.exe","$EvidenceDir/stripped.exe","$EvidenceDir/crt.exe")) {
        $receipt += "artifact { path `"$($path.Replace('\','/'))`" sha256 $((Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLower()) }"
    }
    Write-Utf8 "$EvidenceDir/native-fixtures.sdn" (($receipt -join "`n") + "`n")
    Write-Output "Native fixture build/run evidence: $EvidenceDir/native-fixtures.sdn"
    exit 0
}
if (!(Test-Path -LiteralPath "$EvidenceDir/native-fixtures.sdn")) { throw 'Run Prepare once first; Check reuses its preserved native evidence.' }
$helper = "$repo/scripts/check/lib/extern-census-symbol-sources.shs".Replace('\','/')
$check = @'
set -eu
. "$1"
EXTERN_CENSUS_NM="$2/llvm-nm.exe"
EXTERN_CENSUS_READOBJ="$2/llvm-readobj.exe"
W=$3
census_host_windows || { echo 'Windows host required' >&2; exit 1; }
census_collect_primary "$W/full.exe" "$W/full-symbols.txt" "$W"
grep -qx rt_census_private "$W/full-symbols.txt"
mkdir -p "$W/selected release/bin/release/x86_64-pc-windows-msvc"
cp "$W/full.exe" "$W/selected release/bin/release/x86_64-pc-windows-msvc/simple.exe"
test "$(census_select_binary "$W/selected release")" = "$W/selected release/bin/release/x86_64-pc-windows-msvc/simple.exe"
SIMPLE_BIN="$W/full.exe"
test "$(census_select_binary "$W/selected release")" = "$W/full.exe"
unset SIMPLE_BIN
"$EXTERN_CENSUS_READOBJ" --coff-exports "$W/stripped.exe" > "$W/stripped-exports.txt"
test "$(grep -c '  Name: rt_census_export_' "$W/stripped-exports.txt")" -eq 150
census_collect_primary "$W/stripped.exe" "$W/stripped-symbols.txt" "$W" 2> "$W/stripped-error.log"
grep -q 'PE export table' "$W/stripped-error.log"
grep -qx rt_census_export_1 "$W/stripped-symbols.txt"
# A producer can emit plausible partial output before failing. Its status
# remains authoritative even when the symbol count exceeds the floor.
cat > "$W/failing-nm.sh" <<'TOOL'
#!/bin/sh
"$CENSUS_REAL_NM" "$@"
exit 7
TOOL
chmod +x "$W/failing-nm.sh"
export CENSUS_REAL_NM="$EXTERN_CENSUS_NM"
EXTERN_CENSUS_NM="$W/failing-nm.sh"
if census_collect_primary "$W/full.exe" "$W/partial-symbols.txt" "$W" 2> "$W/partial-error.log"; then
    echo 'partial stdout from failed nm wrongly accepted' >&2; exit 1
fi
grep -q 'acquisition failed' "$W/partial-error.log"
EXTERN_CENSUS_NM="$CENSUS_REAL_NM"
census_collect_system "$W/system-symbols.txt" "$W"
grep -qx malloc "$W/system-symbols.txt"
grep -qx free "$W/system-symbols.txt"
test "$CENSUS_SYSTEM_CLASS" = windows_crt_export
EXTERN_CENSUS_BIN_SYM_FLOOR=0
if census_collect_primary "$W/full.exe" "$W/zero-symbols.txt" "$W" 2> "$W/zero-error.log"; then
    echo 'zero floor wrongly accepted' >&2; exit 1
fi
unset EXTERN_CENSUS_BIN_SYM_FLOOR
EXTERN_CENSUS_WINDOWS_CRT="$W/absent.dll"
if census_collect_system "$W/absent-symbols.txt" "$W" 2> "$W/absent-error.log"; then
    echo 'missing CRT wrongly accepted' >&2; exit 1
fi
echo 'PASS focused Windows symbol-source assertions (not whole census or compiler qualification)'
'@
$bounds = @'
census_collect_primary "$W/full.exe" "$W/header-positive-symbols.txt" "$W"
grep -qx rt_census_private "$W/header-positive-symbols.txt"
EXTERN_CENSUS_BIN_SYM_FLOOR=99999999999999999999999999999999999
if census_collect_primary "$W/full.exe" "$W/oversized-symbols.txt" "$W" 2> "$W/oversized-error.log"; then
    echo 'oversized floor wrongly accepted' >&2; exit 1
fi
unset EXTERN_CENSUS_BIN_SYM_FLOOR
cat > "$W/malformed-readobj.sh" <<'TOOL'
#!/bin/sh
printf '%s\n' 'Format: COFF-x86-64' '  SymbolCount: 152' '  IMAGE_FILE_EXECUTABLE_IMAGE (0x2)'
TOOL
chmod +x "$W/malformed-readobj.sh"
EXTERN_CENSUS_READOBJ="$W/malformed-readobj.sh"
if census_collect_primary "$W/full.exe" "$W/malformed-symbols.txt" "$W" 2> "$W/malformed-error.log"; then
    echo 'COFF header without symbol pointer wrongly accepted' >&2; exit 1
fi
cat > "$W/malformed-readobj.sh" <<'TOOL'
#!/bin/sh
printf '%s\n' 'Format: COFF-x86-64' '  SymbolCount: 152' '  PointerToSymbolTable: 0x4800'
TOOL
if census_collect_primary "$W/full.exe" "$W/nonimage-symbols.txt" "$W" 2> "$W/nonimage-error.log"; then
    echo 'non-executable COFF header wrongly accepted' >&2; exit 1
fi
echo 'PASS oversized floor and malformed COFF admission assertions'
'@
if ($Phase -eq 'CheckBounds') {
    $check = "set -eu`n. `"`$1`"`nEXTERN_CENSUS_NM=`"`$2/llvm-nm.exe`"`nEXTERN_CENSUS_READOBJ=`"`$2/llvm-readobj.exe`"`nW=`$3`n" + $bounds
} else { $check += "`n" + $bounds }
$checkName = if ($Phase -eq 'CheckBounds') { 'check-bounds' } else { 'check' }
Write-Utf8 "$EvidenceDir/$checkName.sh" ($check.Replace("`r",'') + "`n")
Invoke-Checked $Bash @("$EvidenceDir/$checkName.sh",$helper,$LlvmBin,$EvidenceDir) "$EvidenceDir/$checkName.log"
Get-Content -LiteralPath "$EvidenceDir/$checkName.log"
