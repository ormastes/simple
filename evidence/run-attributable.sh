#!/bin/sh
# Launch a long command so that its DEATH IS ATTRIBUTABLE.
#
# Why: two long runs on this box died with no verdict and no in-script kill
# site (a seed cargo build; an earlier Stage 2 RC=143). A missing exit code is
# indistinguishable from a crash, a timeout, and an external kill — so the run
# that matters must record its own identity, a heartbeat, and any catchable
# signal, independent of whoever is watching from outside.
#
#   sh evidence/run-attributable.sh <tag> <command...>
#
# Emits, next to the command log:
#   <tag>.meta      pid/pgid/sid/start, so an outside observer can name it
#   <tag>.beat      heartbeat + process-state samples every 30s
#   <tag>.rc        the ONLY authoritative verdict: RC=<n>, or SIGNAL=<name>
#
# Reading the outcome (in order):
#   RC=<n> present            -> real exit status, trust it. RC=124 is a TIMEOUT.
#   SIGNAL=TERM/INT/HUP       -> a catchable external kill; the signal names it
#   neither present           -> SIGKILL or the process group was reaped.
#                                Last .beat sample brackets time of death to 30s.
set -u
tag=$1; shift
dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
meta="$dir/$tag.meta"; beat="$dir/$tag.beat"; rcf="$dir/$tag.rc"; log="$dir/$tag.log"
rm -f "$meta" "$beat" "$rcf"

# A catchable kill must leave a name behind. SIGKILL cannot be trapped -- that
# is the point: its signature is the ABSENCE of every line below.
for sig in TERM INT HUP QUIT; do
    trap "echo \"SIGNAL=$sig at \$(date -u +%H:%M:%S)\" >> '$rcf'; exit 143" "$sig"
done

"$@" > "$log" 2>&1 &
cmd_pid=$!

{
    echo "tag=$tag"
    echo "cmd=$*"
    echo "wrapper_pid=$$"
    echo "cmd_pid=$cmd_pid"
    echo "pgid=$(ps -o pgid= -p $cmd_pid 2>/dev/null | tr -d ' ')"
    echo "sid=$(awk "{print \$6}" /proc/$cmd_pid/stat 2>/dev/null)"
    echo "start_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "log=$log"
} > "$meta"

# Heartbeat: an independent record of liveness that does NOT depend on the
# command writing anything. cargo block-buffers to a non-tty, so a static
# command log is not evidence of a stall -- this is.
( while kill -0 "$cmd_pid" 2>/dev/null; do
      printf '%s alive load=%s freeGB=%s rss_kb=%s children=%s\n' \
        "$(date -u +%H:%M:%S)" \
        "$(cut -d' ' -f1 /proc/loadavg)" \
        "$(free -g | awk '/^Mem:/{print $7}')" \
        "$(ps -o rss= -p "$cmd_pid" 2>/dev/null | tr -d ' ')" \
        "$(pgrep -P "$cmd_pid" 2>/dev/null | wc -l)" >> "$beat"
      sleep 30
  done ) &
beat_pid=$!

wait "$cmd_pid"; rc=$?
echo "RC=$rc at $(date -u +%H:%M:%S)" >> "$rcf"
kill "$beat_pid" 2>/dev/null
exit "$rc"
