param([Parameter(Mandatory=$true)][string]$Compiler,
      [Parameter(Mandatory=$true)][string]$OutputDirectory)
$ErrorActionPreference = 'Stop'
if (-not (Test-Path -LiteralPath $Compiler) -or -not $env:INCLUDE -or -not $env:LIB) { throw 'pinned compiler and MSVC authority required' }
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$output = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $output) { throw 'qualification output must be new' }
New-Item -ItemType Directory -Path $output | Out-Null
$platform = Join-Path $repo 'src/runtime/platform/platform_win.h'
$helper = Join-Path $repo 'src/runtime/platform/runtime_win_long_path.h'
$source = [IO.File]::ReadAllText($platform)
$begin = $source.IndexOf('#include "runtime_win_long_path.h"')
if ($begin -lt 0) { throw 'provider boundary absent' }
$end = $source.IndexOf('/* C-string worker.', $begin)
if ($end -le $begin) { throw 'provider boundary absent' }
$provider = $source.Substring($begin, $end-$begin)
$harness = @'
#include <windows.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
PROVIDER_SOURCE
int wmain(int argc,wchar_t** argv) {
    if(argc!=2) return 64;
    int n=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,argv[1],-1,NULL,0,NULL,NULL);
    if(n<=0) return 65;
    char* path=malloc(n); if(!path) return 66;
    if(!WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,argv[1],-1,path,n,NULL,NULL)) { free(path); return 67; }
    bool ok=rt_dir_remove_all_impl(path); free(path); return ok?0:1;
}
'@
[IO.File]::WriteAllText((Join-Path $output 'provider.c'), $harness.Replace('PROVIDER_SOURCE',$provider))
Copy-Item -LiteralPath $helper -Destination (Join-Path $output 'runtime_win_long_path.h')
Push-Location $output
try {
    & $Compiler '/nologo' '/O2' '/D_CRT_SECURE_NO_WARNINGS' 'provider.c' '/Fe:provider.exe' '-fuse-ld=lld' *> 'build.log'
    if ($LASTEXITCODE -ne 0) { throw 'native build failed; inspect build.log' }
} finally { Pop-Location }
$outside = Join-Path $output 'separate-target'
$scope = Join-Path $output ('owned-scope-' + [char]::ConvertFromUtf32(0x1F331))
New-Item -ItemType Directory -Path $outside,$scope | Out-Null
Set-Content -LiteralPath (Join-Path $outside 'sentinel.txt') -Value 'must-survive'
New-Item -ItemType Junction -Path (Join-Path $scope 'nested-junction') -Target $outside | Out-Null
Set-Content -LiteralPath (Join-Path $scope ('owned-' + [char]::ConvertFromUtf32(0x1F331) + '.txt')) -Value 'must-remove'
if (-not $scope.StartsWith($output + [IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)) { throw 'scope escaped output' }
& (Join-Path $output 'provider.exe') $scope
$code = $LASTEXITCODE
$removed = -not (Test-Path -LiteralPath $scope)
$survived = Test-Path -LiteralPath (Join-Path $outside 'sentinel.txt')
Get-FileHash -Algorithm SHA256 -LiteralPath $platform,$helper,(Join-Path $output 'provider.c'),(Join-Path $output 'provider.exe') | Format-List | Out-File (Join-Path $output 'hashes.txt')
"exit=$code unicode_scope_removed=$removed external_sentinel_survived=$survived" | Out-File (Join-Path $output 'result.txt')
if ($code -ne 0 -or -not $removed -or -not $survived) { throw 'native containment regression failed' }
Write-Output 'STATUS: PASS (provider-only native Unicode/junction containment)'
