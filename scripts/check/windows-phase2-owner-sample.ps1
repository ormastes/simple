param([switch]$Launch)
$root = 'C:/w2ladder'
if ($Launch) {
    $proc = Start-Process -FilePath (Get-Process -Id $PID).Path -ArgumentList @('-NoProfile','-File',$PSCommandPath) -WindowStyle Hidden -PassThru
    $proc.Id | Set-Content "$root/sampler.pid"
    exit 0
}
$deadline = [DateTime]::UtcNow.AddSeconds(940)
while ([DateTime]::UtcNow -lt $deadline -and -not (Test-Path "$root/sample.stop")) {
    $all = @(Get-CimInstance Win32_Process)
    $selected = @{}
    foreach ($p in $all) {
        if ($p.ExecutablePath -eq 'C:\w2tuple\compiler\simple_stage2.exe') { $selected[[int]$p.ProcessId] = $true }
    }
    for ($depth=0; $depth -lt 8; $depth++) {
        foreach ($p in $all) { if ($selected.ContainsKey([int]$p.ParentProcessId)) { $selected[[int]$p.ProcessId]=$true } }
    }
    $rows = @()
    foreach ($p in $all) {
        if ($selected.ContainsKey([int]$p.ProcessId)) {
            $live = Get-Process -Id $p.ProcessId -ErrorAction SilentlyContinue
            $rows += @{pid=$p.ProcessId; parent=$p.ParentProcessId; executable=$p.ExecutablePath; command=$p.CommandLine; cpu_seconds=$live.CPU; working_set=$live.WorkingSet64}
        }
    }
    @{utc=[DateTime]::UtcNow.ToString('o'); processes=$rows} | ConvertTo-Json -Depth 4 -Compress | Add-Content "$root/process-samples.jsonl"
    Start-Sleep -Seconds 5
}
