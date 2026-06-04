#!/bin/sh
set -eu

request_path="$1"
if [ ! -f "$request_path" ]; then
    echo "rtk_mock_runner: request file not found: $request_path" >&2
    exit 1
fi

result_path="$(grep '^result_path=' "$request_path" | cut -d= -f2-)"
checkpoint_path="$(grep '^checkpoint_path=' "$request_path" | cut -d= -f2-)"
max_cycles="$(grep '^max_cycles=' "$request_path" | cut -d= -f2-)"

if [ -z "$result_path" ] || [ -z "$checkpoint_path" ] || [ -z "$max_cycles" ]; then
    echo "rtk_mock_runner: request is missing required fields" >&2
    exit 1
fi
if [ ! -f "$checkpoint_path" ]; then
    echo "rtk_mock_runner: checkpoint file not found: $checkpoint_path" >&2
    exit 1
fi

pc="$(grep '^pc=' "$checkpoint_path" | cut -d= -f2-)"
cycle_count="$(grep '^cycle_count=' "$checkpoint_path" | cut -d= -f2-)"
reg_values="$(grep '^reg_values=' "$checkpoint_path" | cut -d= -f2-)"

if [ -z "$pc" ] || [ -z "$cycle_count" ] || [ -z "$reg_values" ]; then
    echo "rtk_mock_runner: checkpoint is missing required fields" >&2
    exit 1
fi

next_cycles=$((cycle_count + max_cycles))
next_pc=$((pc + 4))
next_regs="$(printf '%s\n' "$reg_values" | sed 's/^\[//; s/\]$//' | awk -F, 'BEGIN { OFS="," } { for (i = 1; i <= NF; i++) { gsub(/^[[:space:]]+|[[:space:]]+$/, "", $i) } if (NF >= 11) { $11 = 99 } print "[" $0 "]" }')"

cat > "$result_path" <<EOF
pc=$next_pc
cycle_count=$next_cycles
halted=true
reg_values=$next_regs
reg[10]=99
EOF
