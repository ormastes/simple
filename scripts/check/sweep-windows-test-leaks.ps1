param([int]$AgeMinutes = 5, [switch]$Kill)
$all = Get-CimInstance Win32_Process -Filter "Name='simple.exe'"
$ml = $all | Where-Object { $_.ExecutablePath -like '*mainlane*' }
$old = $ml | Where-Object { $_.CreationDate -lt (Get-Date).AddMinutes(-$AgeMinutes) }
$testers = @($old | Where-Object { $_.CommandLine -match ' test ' })
$leaks = @($old | Where-Object { $_.CommandLine -notmatch ' test ' })
Write-Output ("total_simple=" + $all.Count + " mainlane=" + $ml.Count + " old=" + $old.Count + " old_testers=" + $testers.Count + " old_leaks=" + $leaks.Count)
if ($Kill) {
  $leaks | ForEach-Object { Stop-Process -Id $_.ProcessId -Force -ErrorAction SilentlyContinue }
  Write-Output ("killed_leaks=" + $leaks.Count)
  $leaks | Select-Object -First 8 ProcessId, @{n='Cmd';e={ if ($_.CommandLine) { $_.CommandLine.Substring(0, [Math]::Min(90, $_.CommandLine.Length)) } else { '' } }} | Format-Table -AutoSize | Out-String -Width 200
}
