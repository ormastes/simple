param([Parameter(Mandatory=$true)][int]$BatchProcessId,[Parameter(Mandatory=$true)][int]$OwnerProcessId)
$ErrorActionPreference='Stop'
$rows=@()
$ancestor=$BatchProcessId
for($depth=0;$depth -lt 32 -and $ancestor -gt 0;$depth++) {
    $row=Get-CimInstance Win32_Process -Filter "ProcessId=$ancestor"
    if(!$row){throw 'Process ancestry disappeared during observation.'}
    $live=Get-Process -Id $ancestor -ErrorAction Stop
    $rows+=@{pid=[int]$row.ProcessId;parent_pid=[int]$row.ParentProcessId;start_utc=$live.StartTime.ToUniversalTime().ToString('o');command_line=[string]$row.CommandLine}
    if($ancestor -eq $OwnerProcessId){break}
    $ancestor=[int]$row.ParentProcessId
}
ConvertTo-Json -InputObject $rows -Depth 4 -Compress
