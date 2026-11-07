param(
    [Parameter(Mandatory=$true)][string]$Compiler,
    [Parameter(Mandatory=$true)][string]$Linker,
    [Parameter(Mandatory=$true)][string]$SdkLibDirectory,
    [Parameter(Mandatory=$true)][string]$VcLibDirectory,
    [Parameter(Mandatory=$true)][string]$OutputDirectory
)
$ErrorActionPreference = 'Stop'
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$output = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $output) { throw 'use a fresh output directory to retain independent evidence' }
[IO.Directory]::CreateDirectory($output) | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)

function Invoke-Bounded($tool, [string[]]$arguments, $label, $seconds) {
    $start = [Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $tool
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.Arguments = (($arguments | ForEach-Object {
        if ($_.Contains('"')) { throw 'fixture arguments must not contain quotes' }
        '"' + $_ + '"'
    }) -join ' ')
    $process = [Diagnostics.Process]::Start($start)
    try {
        $stdout = $process.StandardOutput.ReadToEndAsync()
        $stderr = $process.StandardError.ReadToEndAsync()
        if (!$process.WaitForExit($seconds * 1000)) {
            $process.Kill()
            $process.WaitForExit()
            throw "timeout in $label"
        }
        if (![Threading.Tasks.Task]::WaitAll([Threading.Tasks.Task[]]@($stdout,$stderr),5000)) {
            throw "output drain timed out in $label"
        }
        [IO.File]::WriteAllText((Join-Path $output "$label.log"),$stdout.Result + $stderr.Result,$utf8)
        return $process.ExitCode
    } finally {
        if (!$process.HasExited) { $process.Kill() }
        $process.Dispose()
    }
}

# Read the actual default list, not a second expected library inventory.
$owner = Join-Path $root 'src/compiler/70.backend/linker/msvc.spl'
$ownerText = [IO.File]::ReadAllText($owner)
$match = [regex]::Match($ownerText,'(?m)^fn default_windows_libs_with_suffix\(\) -> \[text\]:\r?\n[ \t]+(\[[^\r\n]+\])\r?$')
if (!$match.Success) { throw 'MSVC default library owner is not the expected explicit list' }
$libraries = @([regex]::Matches($match.Groups[1].Value,'"([^"\r\n]+\.lib)"') | ForEach-Object { $_.Groups[1].Value })
if ($libraries.Count -eq 0) { throw 'empty default library list' }
$source = Join-Path $output 'winhttp_session.c'
$object = Join-Path $output 'winhttp_session.obj'
[IO.File]::WriteAllText($source,@'
__declspec(dllimport) void* __stdcall WinHttpOpen(const unsigned short*, unsigned long, const unsigned short*, const unsigned short*, unsigned long);
__declspec(dllimport) int __stdcall WinHttpCloseHandle(void*);
__declspec(dllimport) void __stdcall ExitProcess(unsigned int);
void mainCRTStartup(void) {
    static const unsigned short agent[] = {'s','i','m','p','l','e',0};
    void* session = WinHttpOpen(agent, 1, 0, 0, 0);
    if (!session) ExitProcess(1);
    if (!WinHttpCloseHandle(session)) ExitProcess(2);
    ExitProcess(0);
}
'@,$utf8)
if ((Invoke-Bounded $Compiler @('/nologo','/c','/GS-','/Zl',"/Fo$object",$source) 'compile' 30) -ne 0) { throw 'fixture compilation failed' }
$common = @('/NOLOGO','/NODEFAULTLIB','/MACHINE:X64','/SUBSYSTEM:CONSOLE','/ENTRY:mainCRTStartup',$object,
    "/LIBPATH:$SdkLibDirectory/um/x64","/LIBPATH:$SdkLibDirectory/ucrt/x64","/LIBPATH:$VcLibDirectory")
$negative = Join-Path $output 'without_winhttp.exe'
$negativeLibraries = @($libraries | Where-Object { $_ -ne 'winhttp.lib' })
$negativeStatus = Invoke-Bounded $Linker ($common + $negativeLibraries + "/OUT:$negative") 'negative-link' 30
$negativeLog = [IO.File]::ReadAllText((Join-Path $output 'negative-link.log'))
if ($negativeStatus -eq 0 -or $negativeLog -notmatch 'undefined symbol:.*WinHttp(Open|CloseHandle)') {
    throw 'negative control did not reject the missing WinHTTP imports'
}
$positive = Join-Path $output 'with_default_libraries.exe'
if ((Invoke-Bounded $Linker ($common + $libraries + "/OUT:$positive") 'positive-link' 30) -ne 0) { throw 'default library link failed' }
if ((Invoke-Bounded $positive @() 'run' 5) -ne 0) { throw 'local WinHTTP session lifecycle failed' }
[IO.File]::WriteAllText((Join-Path $output 'result.sdn'),
    "schema: simple-msvc-winhttp-link-check/v1`nstatus: pass`nnegative_link_status: $negativeStatus`npositive_link_status: 0`nrun_status: 0`nowner_sha256: $((Get-FileHash -LiteralPath $owner -Algorithm SHA256).Hash.ToLowerInvariant())`n",$utf8)
Write-Output 'PASS: MSVC default WinHTTP libraries, missing-library control and local session lifecycle'
