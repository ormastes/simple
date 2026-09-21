# Read only the timeout wrapper's direct-child workload session. ps uses MSYS
# PIDs; /proc stat uses those same PIDs and reports RSS in 4 KiB units, even
# when getconf PAGESIZE reports the 64 KiB Windows allocation granularity.
# This sampler is called only on MINGW/MSYS/CYGWIN, never on native POSIX hosts.
function stat_read(pid, path, line, actual, count, result) {
    path = proc_root "/" pid "/stat"
    result = (getline line < path)
    close(path)
    if (result < 1) return 0
    actual = line
    sub(/ .*/, "", actual)
    if (actual != pid || line !~ /\) /) return -1
    # comm can contain spaces and closing parentheses. The final ') ' ends it.
    sub(/^.*\) /, "", line)
    count = split(line, stat, " ")
    if (count < 22 || stat[2] !~ /^[0-9]+$/ || stat[3] !~ /^[0-9]+$/ ||
        stat[20] !~ /^[0-9]+$/ || stat[22] !~ /^[0-9]+$/) return -1
    return 1
}
function alive() { return stat[1] != "Z" && stat[1] != "X" }
BEGIN {
    invalid = 0
    if (root !~ /^[1-9][0-9]*$/ || stat_read(root) != 1 || !alive()) {
        invalid = 1
        exit 1
    }
    root_started = stat[20]
}
$1 ~ /^[1-9][0-9]*$/ && $2 ~ /^[0-9]+$/ && $3 ~ /^[0-9]+$/ {
    pid = $1
    if (pid in parent && (parent[pid] != $2 || group[pid] != $3)) invalid = 1
    parent[pid] = $2
    group[pid] = $3
}
END {
    if (invalid) exit 1
    leader = 0
    for (pid in parent) {
        if (parent[pid] == root && group[pid] == pid) {
            if (leader) exit 1
            leader = pid
        }
    }
    if (!leader || stat_read(leader) != 1 || !alive() ||
        stat[2] != root || stat[3] != leader) exit 1
    leader_started = stat[20]
    pages = 0
    # Associative PID keys deduplicate ps rows. Membership is checked again
    # against /proc so stale ps rows cannot count an unrelated process group.
    for (pid in group) {
        if (group[pid] != leader) continue
        result = stat_read(pid)
        if (result < 0) exit 1
        if (result == 1 && alive() && stat[3] == leader) pages += stat[22]
    }
    # Discard a sample if its wrapper or session leader exits/is reused during
    # collection. Missing/ambiguous authority never produces a numeric zero.
    if (stat_read(leader) != 1 || !alive() || stat[20] != leader_started ||
        stat[2] != root || stat[3] != leader) exit 1
    if (stat_read(root) != 1 || !alive() || stat[20] != root_started) exit 1
    if (pages <= 0) exit 1
    printf "%.0f\n", pages * 4
}
