param(
    [Parameter(Mandatory=$true)][string]$Compiler,
    [Parameter(Mandatory=$true)][string]$Linker,
    [Parameter(Mandatory=$true)][string]$VcRoot,
    [Parameter(Mandatory=$true)][string]$SdkRoot,
    [string]$SdkVersion = '10.0.26100.0',
    [Parameter(Mandatory=$true)][string]$OutputDirectory
)
$ErrorActionPreference = 'Stop'
if ($env:OS -ne 'Windows_NT') { throw 'UNSUPPORTED: native Windows required' }
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../..'))
$output = [IO.Path]::GetFullPath($OutputDirectory)
$buildRoot = [IO.Path]::GetFullPath((Join-Path $root 'build')) + [IO.Path]::DirectorySeparatorChar
if (!$output.StartsWith($buildRoot,[StringComparison]::OrdinalIgnoreCase)) { throw 'output must remain in this isolated checkout build directory' }
if (Test-Path -LiteralPath $output) { throw 'use a fresh output directory; preserve earlier receipts' }
[IO.Directory]::CreateDirectory($output) | Out-Null
$utf8 = [Text.UTF8Encoding]::new($false)

function Quote-Sdn([string]$value) { '"' + $value.Replace('\','\\').Replace('"','\"').Replace("`r",'\r').Replace("`n",'\n') + '"' }
function Invoke-Bounded([string]$tool,[string[]]$arguments,[string]$label,[int]$seconds) {
    $start = [Diagnostics.ProcessStartInfo]::new()
    $start.FileName = $tool
    $start.WorkingDirectory = $output
    $start.UseShellExecute = $false
    $start.CreateNoWindow = $true
    $start.RedirectStandardOutput = $true
    $start.RedirectStandardError = $true
    $start.Arguments = (($arguments | ForEach-Object {
        if ($_.Contains('"')) { throw 'native harness arguments cannot contain embedded quotes' }
        '"' + $_ + '"'
    }) -join ' ')
    $command = 'tool: ' + (Quote-Sdn $tool) + "`narguments: [" + (($arguments | ForEach-Object { Quote-Sdn $_ }) -join ', ') + "]`n"
    [IO.File]::WriteAllText((Join-Path $output "$label.command.sdn"),$command,$utf8)
    $process = [Diagnostics.Process]::Start($start)
    try {
        $stdout = $process.StandardOutput.ReadToEndAsync()
        $stderr = $process.StandardError.ReadToEndAsync()
        if (!$process.WaitForExit($seconds * 1000)) {
            $process.Kill()
            $process.WaitForExit()
            throw "timeout in $label"
        }
        if (![Threading.Tasks.Task]::WaitAll([Threading.Tasks.Task[]]@($stdout,$stderr),5000)) { throw "output drain timed out in $label" }
        [IO.File]::WriteAllText((Join-Path $output "$label.stdout.log"),$stdout.Result,$utf8)
        [IO.File]::WriteAllText((Join-Path $output "$label.stderr.log"),$stderr.Result,$utf8)
        [IO.File]::WriteAllText((Join-Path $output "$label.status"),[string]$process.ExitCode,$utf8)
        return [int]$process.ExitCode
    } finally {
        if (!$process.HasExited) { $process.Kill() }
        $process.Dispose()
    }
}

$source = Join-Path $root 'src/runtime/test/runtime_process_owned_windows_adapter_selfcheck.c'
$owner = Join-Path $root 'src/runtime/runtime_process_owned.c'
$inputs = @($source,$owner,(Join-Path $root 'src/runtime/runtime.h'),(Join-Path $root 'src/runtime/runtime_nonnull.h'))
$inputs += @(Get-ChildItem (Join-Path $root 'src/runtime') -Filter 'runtime_process_owned*private.h' | ForEach-Object { $_.FullName })
$before = @{}
foreach ($inputPath in $inputs) { $before[$inputPath] = (Get-FileHash -LiteralPath $inputPath -Algorithm SHA256).Hash.ToLower() }
$object = Join-Path $output 'adapter.obj'
$binary = Join-Path $output 'opaque adapter selfcheck.exe'
$flags = @('/nologo','/c','/std:c11','/O1','/MT','/W4','/utf-8','/D_WIN32_WINNT=0x0A00','/D_CRT_SECURE_NO_WARNINGS',
    '/clang:-ferror-limit=5',"/I$VcRoot/include","/I$SdkRoot/Include/$SdkVersion/ucrt",
    "/I$SdkRoot/Include/$SdkVersion/shared","/I$SdkRoot/Include/$SdkVersion/um", "/Fo$object",$source)
if ((Invoke-Bounded $Compiler $flags 'compile' 90) -ne 0) { throw 'native adapter compilation failed; inspect retained logs' }
$link = @('/NOLOGO','/SUBSYSTEM:CONSOLE','/MACHINE:X64',"/OUT:$binary",$object,
    "/LIBPATH:$VcRoot/lib/x64","/LIBPATH:$SdkRoot/Lib/$SdkVersion/ucrt/x64","/LIBPATH:$SdkRoot/Lib/$SdkVersion/um/x64",
    'libcmt.lib','libvcruntime.lib','libucrt.lib','oldnames.lib','kernel32.lib','advapi32.lib')
if ((Invoke-Bounded $Linker $link 'link' 30) -ne 0) { throw 'native adapter link failed; inspect retained logs' }
if ((Invoke-Bounded $binary @() 'run' 30) -ne 0) { throw 'native adapter assertions failed; inspect retained logs' }
$run = [IO.File]::ReadAllText((Join-Path $output 'run.stdout.log'))
$match = [regex]::Match($run,'(?m)^PASS Windows opaque process adapter checks=([1-9][0-9]*)\r?$')
if (!$match.Success) { throw 'native execution produced no positive assertion count' }
foreach ($inputPath in $inputs) {
    if ((Get-FileHash -LiteralPath $inputPath -Algorithm SHA256).Hash.ToLower() -ne $before[$inputPath]) { throw "source changed during run: $inputPath" }
}
$receipt = @(
    'schema: windows-owned-process-adapter-native/v1'
    'status: PASS'
    'scope: native C opaque adapter and small value host only'
    'self_hosted_simple_qualification: NOT_RUN'
    'production_runtime_modified: false'
    "assertions: $($match.Groups[1].Value)"
    ('compiler: ' + (Quote-Sdn $Compiler))
    ('compiler_sha256: ' + (Get-FileHash -LiteralPath $Compiler -Algorithm SHA256).Hash.ToLower())
    ('linker: ' + (Quote-Sdn $Linker))
    ('linker_sha256: ' + (Get-FileHash -LiteralPath $Linker -Algorithm SHA256).Hash.ToLower())
    ('vc_root: ' + (Quote-Sdn $VcRoot))
    ('sdk_root: ' + (Quote-Sdn $SdkRoot))
    "sdk_version: $SdkVersion"
    ('executable_sha256: ' + (Get-FileHash -LiteralPath $binary -Algorithm SHA256).Hash.ToLower())
    'sources |path, sha256|'
)
foreach ($inputPath in $inputs) { $receipt += '    ' + (Quote-Sdn $inputPath) + ', ' + $before[$inputPath] }
[IO.File]::WriteAllText((Join-Path $output 'qualification.sdn'),($receipt -join "`n") + "`n",$utf8)
Write-Output "PASS native Windows opaque adapter assertions=$($match.Groups[1].Value); self-hosted Simple qualification NOT_RUN"
