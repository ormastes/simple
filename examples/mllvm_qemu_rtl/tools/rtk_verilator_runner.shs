#!/bin/sh
set -eu

request_path="$1"
if [ ! -f "$request_path" ]; then
    echo "rtk_verilator_runner: request file not found: $request_path" >&2
    exit 1
fi

field() {
    key="$1"
    grep "^${key}=" "$request_path" | cut -d= -f2-
}

reg_read() {
    idx="$1"
    printf '%s\n' "$reg_values" | sed 's/^\[//; s/\]$//' | awk -F, -v idx="$((idx + 1))" '{ gsub(/^[[:space:]]+|[[:space:]]+$/, "", $idx); print $idx }'
}

reg_write() {
    idx="$1"
    value="$2"
    if [ "$idx" -eq 0 ]; then
        printf '%s\n' "$reg_values" | sed 's/^\[//; s/\]$//' | awk -F, 'BEGIN { OFS="," } { for (i = 1; i <= NF; i++) { gsub(/^[[:space:]]+|[[:space:]]+$/, "", $i) } if (NF >= 1) { $1 = 0 } print "[" $0 "]" }'
        return
    fi
    printf '%s\n' "$reg_values" | sed 's/^\[//; s/\]$//' | awk -F, -v rd="$((idx + 1))" -v dest="$value" 'BEGIN { OFS="," } { for (i = 1; i <= NF; i++) { gsub(/^[[:space:]]+|[[:space:]]+$/, "", $i) } if (rd >= 1 && rd <= NF) { $rd = dest } if (NF >= 1) { $1 = 0 } print "[" $0 "]" }'
}

mem_read_word() {
    addr="$1"
    if [ ! -f "$mem_file" ]; then
        echo 0
        return
    fi
    val="$(awk -F= -v want="$addr" '$1 == want { print $2 }' "$mem_file" | tail -n 1)"
    if [ -z "$val" ]; then
        echo 0
    else
        echo "$val"
    fi
}

mem_write_word() {
    addr="$1"
    value="$2"
    tmp_file="${mem_file}.tmp"
    if [ -f "$mem_file" ]; then
        awk -F= -v want="$addr" '$1 != want { print $0 }' "$mem_file" > "$tmp_file"
    else
        : > "$tmp_file"
    fi
    printf '%s=%s\n' "$addr" "$value" >> "$tmp_file"
    mv "$tmp_file" "$mem_file"
}

checkpoint_path="$(field checkpoint_path)"
result_path="$(field result_path)"
max_cycles="$(field max_cycles)"
inst_word="$(field inst_word)"
top_module="$(field top_module)"
top_source="$(field top_source)"
work_dir="$(dirname "$request_path")"
mem_file="${work_dir}/stub_memory.sdn"

if [ -z "$checkpoint_path" ] || [ -z "$result_path" ] || [ -z "$max_cycles" ] || [ -z "$inst_word" ] || [ -z "$top_module" ] || [ -z "$top_source" ]; then
    echo "rtk_verilator_runner: request is missing required fields" >&2
    exit 1
fi
if [ ! -f "$checkpoint_path" ]; then
    echo "rtk_verilator_runner: checkpoint file not found: $checkpoint_path" >&2
    exit 1
fi
if [ ! -f "$top_source" ]; then
    cat > "$result_path" <<EOF
status=error
message=RTL top source not found: $top_source
EOF
    exit 2
fi

pc="$(grep '^pc=' "$checkpoint_path" | cut -d= -f2-)"
cycle_count="$(grep '^cycle_count=' "$checkpoint_path" | cut -d= -f2-)"
read_count="$(grep '^read_count=' "$checkpoint_path" | cut -d= -f2-)"
write_count="$(grep '^write_count=' "$checkpoint_path" | cut -d= -f2-)"
reg_values="$(grep '^reg_values=' "$checkpoint_path" | cut -d= -f2-)"

if [ -z "$pc" ] || [ -z "$cycle_count" ] || [ -z "$read_count" ] || [ -z "$write_count" ] || [ -z "$reg_values" ]; then
    cat > "$result_path" <<EOF
status=error
message=checkpoint is missing required fields
EOF
    exit 2
fi

if [ "$cycle_count" -eq 0 ] && [ -f "$mem_file" ]; then
    rm -f "$mem_file"
fi

if [ "$(basename "$top_source")" = "picorv32_stub.v" ]; then
    opcode=$((inst_word & 127))
    rd=$(((inst_word >> 7) & 31))
    funct3=$(((inst_word >> 12) & 7))
    rs1=$(((inst_word >> 15) & 31))
    rs2=$(((inst_word >> 20) & 31))
    funct7=$(((inst_word >> 25) & 127))
    imm12=$(((inst_word >> 20) & 4095))
    if [ "$imm12" -ge 2048 ]; then
        imm12=$((imm12 - 4096))
    fi
    bimm12=$(((inst_word >> 31) & 1))
    bimm11=$(((inst_word >> 7) & 1))
    bimm10_5=$(((inst_word >> 25) & 63))
    bimm4_1=$(((inst_word >> 8) & 15))
    branch_imm=$(( (bimm12 << 12) | (bimm11 << 11) | (bimm10_5 << 5) | (bimm4_1 << 1) ))
    if [ "$branch_imm" -ge 4096 ]; then
        branch_imm=$((branch_imm - 8192))
    fi
    jimm20=$(((inst_word >> 31) & 1))
    jimm19_12=$(((inst_word >> 12) & 255))
    jimm11=$(((inst_word >> 20) & 1))
    jimm10_1=$(((inst_word >> 21) & 1023))
    jal_imm=$(( (jimm20 << 20) | (jimm19_12 << 12) | (jimm11 << 11) | (jimm10_1 << 1) ))
    if [ "$jal_imm" -ge 1048576 ]; then
        jal_imm=$((jal_imm - 2097152))
    fi

    next_pc=$((pc + 4))
    next_cycles=$((cycle_count + 1))
    next_read_count=$read_count
    next_write_count=$write_count
    result_msg="stub_rtl_step_without_verilator"
    halted=false
    next_regs="$reg_values"

    if [ "$inst_word" -eq 1048691 ]; then
        halted=true
        result_msg="stub_rtl_ebreak"
    elif [ "$opcode" -eq 19 ] && [ "$funct3" -eq 0 ]; then
        src_val="$(reg_read "$rs1")"
        if [ -z "$src_val" ]; then
            src_val=0
        fi
        dest_val=$((src_val + imm12))
        next_regs="$(reg_write "$rd" "$dest_val")"
        result_msg="stub_rtl_addi"
    elif [ "$opcode" -eq 51 ] && [ "$funct3" -eq 0 ] && [ "$funct7" -eq 0 ]; then
        lhs="$(reg_read "$rs1")"
        rhs="$(reg_read "$rs2")"
        if [ -z "$lhs" ]; then lhs=0; fi
        if [ -z "$rhs" ]; then rhs=0; fi
        next_regs="$(reg_write "$rd" "$((lhs + rhs))")"
        result_msg="stub_rtl_add"
    elif [ "$opcode" -eq 51 ] && [ "$funct3" -eq 0 ] && [ "$funct7" -eq 32 ]; then
        lhs="$(reg_read "$rs1")"
        rhs="$(reg_read "$rs2")"
        if [ -z "$lhs" ]; then lhs=0; fi
        if [ -z "$rhs" ]; then rhs=0; fi
        next_regs="$(reg_write "$rd" "$((lhs - rhs))")"
        result_msg="stub_rtl_sub"
    elif [ "$opcode" -eq 99 ] && [ "$funct3" -eq 0 ]; then
        lhs="$(reg_read "$rs1")"
        rhs="$(reg_read "$rs2")"
        if [ -z "$lhs" ]; then lhs=0; fi
        if [ -z "$rhs" ]; then rhs=0; fi
        if [ "$lhs" -eq "$rhs" ]; then
            next_pc=$((pc + branch_imm))
            result_msg="stub_rtl_beq_taken"
        else
            result_msg="stub_rtl_beq_not_taken"
        fi
    elif [ "$opcode" -eq 111 ]; then
        next_regs="$(reg_write "$rd" "$((pc + 4))")"
        next_pc=$((pc + jal_imm))
        result_msg="stub_rtl_jal"
    elif [ "$opcode" -eq 103 ] && [ "$funct3" -eq 0 ]; then
        base="$(reg_read "$rs1")"
        if [ -z "$base" ]; then base=0; fi
        next_regs="$(reg_write "$rd" "$((pc + 4))")"
        next_pc=$(((base + imm12) & -2))
        result_msg="stub_rtl_jalr"
    elif [ "$opcode" -eq 3 ] && [ "$funct3" -eq 2 ]; then
        base="$(reg_read "$rs1")"
        if [ -z "$base" ]; then base=0; fi
        addr=$((base + imm12))
        load_val="$(mem_read_word "$addr")"
        next_regs="$(reg_write "$rd" "$load_val")"
        next_read_count=$((read_count + 1))
        result_msg="stub_rtl_lw"
    elif [ "$opcode" -eq 35 ] && [ "$funct3" -eq 2 ]; then
        simm_hi=$(((inst_word >> 25) & 127))
        simm_lo=$(((inst_word >> 7) & 31))
        store_imm=$(((simm_hi << 5) | simm_lo))
        if [ "$store_imm" -ge 2048 ]; then
            store_imm=$((store_imm - 4096))
        fi
        base="$(reg_read "$rs1")"
        store_val="$(reg_read "$rs2")"
        if [ -z "$base" ]; then base=0; fi
        if [ -z "$store_val" ]; then store_val=0; fi
        addr=$((base + store_imm))
        mem_write_word "$addr" "$store_val"
        next_write_count=$((write_count + 1))
        result_msg="stub_rtl_sw"
    fi
    cat > "$result_path" <<EOF
status=ok
message=$result_msg
pc=$next_pc
cycle_count=$next_cycles
halted=$halted
read_count=$next_read_count
write_count=$next_write_count
reg_values=$next_regs
EOF
    exit 0
fi

verilator_bin="${VERILATOR_BIN:-}"
if [ -z "$verilator_bin" ]; then
    verilator_bin="$(command -v verilator 2>/dev/null || true)"
fi
if [ -z "$verilator_bin" ]; then
    cat > "$result_path" <<EOF
status=error
message=verilator executable not found
EOF
    exit 2
fi

if ! "$verilator_bin" --lint-only --top-module "$top_module" "$top_source" >/tmp/rtk_verilator_runner.stdout 2>/tmp/rtk_verilator_runner.stderr; then
    lint_msg="$(tr '\n' ' ' </tmp/rtk_verilator_runner.stderr | sed 's/[[:space:]]\+/ /g')"
    cat > "$result_path" <<EOF
status=error
message=verilator lint failed: $lint_msg
EOF
    exit 2
fi

cat > "$result_path" <<EOF
status=unimplemented
message=verilator lint ok but RTL stepping harness is not implemented yet
EOF
exit 2
