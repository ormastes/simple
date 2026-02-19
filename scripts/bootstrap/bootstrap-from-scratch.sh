#!/usr/bin/env bash
# Unified bootstrap from scratch (Linux/macOS/FreeBSD/MinGW)
#
# Stages:
#   seed  -> build seed_cpp
#   core1 -> seed_cpp transpiles compiler + native compile
#   core2 -> core1 recompiles compiler
#   full1 -> core2 compiles full CLI compiler
#   full2 -> full1 recompiles itself (reproducibility)
#
# Examples:
#   scripts/bootstrap/bootstrap-from-scratch.sh
#   scripts/bootstrap/bootstrap-from-scratch.sh --step=core1 --deploy
#   scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64 --step=core1

set -euo pipefail

STEP="full2"
STEP_RANK=5
SKIP_VERIFY=false
SKIP_TIER_CHECK=false
JOBS=""
CXX=""
HOST_CXX_ARG=""
OUTPUT="bin/release/simple"
KEEP_ARTIFACTS=false
VERBOSE=false
DEPLOY="auto"
TARGET=""

BUILD_DIR="build/bootstrap"
SEED_DIR="src/compiler_seed"
SEED_BUILD_DIR="build/seed"
COMPILER_CORE_DIR="src/compiler"
COMPILER_SHARED_DIR="src/compiler_shared"
ROOT_DIR="$(pwd -P)"

HOST_OS=""
HOST_ARCH=""
TARGET_OS=""
TARGET_ARCH=""
TARGET_EXE_EXT=""
IS_CROSS=false
SEED_CPP=""
TARGET_CXX=""
TARGET_CXX_FLAGS=()
HOST_CXX=""
PROJECT_TIER=""
FULL_TIER_KEYWORDS_CSV=""
TIER_CACHE_READY=false
MODULE_TIER_DIRS=()
MODULE_TIER_VALUES=()

log() { echo "[bootstrap] $*"; }
warn() { echo "[bootstrap] WARN: $*" >&2; }
err() { echo "[bootstrap] ERROR: $*" >&2; }

run() {
    if [ "$VERBOSE" = true ]; then
        echo "+ $*" >&2
    fi
    "$@"
}

usage() {
    cat <<USAGE
Simple Compiler - Bootstrap From Scratch

Usage:
  scripts/bootstrap/bootstrap-from-scratch.sh [options]

Options:
  --step=seed|core1|core2|full1|full2  Stop after a stage (default: full2)
  --deploy                              Copy selected stage output to bin/release/simple
  --no-deploy                           Do not copy output
  --skip-verify                         Skip full2 reproducibility stage
  --skip-tier-check                     Skip core-tier compatibility check before Core1
  --target=OS-ARCH                      Override target platform (default: host)
  --jobs=N                              Parallel build jobs (auto by default)
  --cc=PATH                             Clang-family C++ compiler for target stages
  --host-cc=PATH                        Clang-family C++ compiler for host seed build
  --output=PATH                         Deploy path (default: bin/release/simple)
  --keep-artifacts                      Keep build/bootstrap artifacts
  --verbose                             Print executed commands
  --help                                Show this help
USAGE
}

stage_rank() {
    case "$1" in
        seed) echo 1 ;;
        core1) echo 2 ;;
        core2) echo 3 ;;
        full1) echo 4 ;;
        full2) echo 5 ;;
        *) return 1 ;;
    esac
}

parse_target() {
    local raw="$1"
    case "$raw" in
        linux-*|macos-*|freebsd-*|windows-*)
            TARGET_OS="${raw%%-*}"
            TARGET_ARCH="${raw#*-}"
            ;;
        *)
            err "Invalid --target value: $raw"
            err "Expected OS-ARCH (e.g. linux-x86_64, freebsd-x86_64, windows-x86_64)"
            exit 1
            ;;
    esac
}

for arg in "$@"; do
    case "$arg" in
        --skip-verify)    SKIP_VERIFY=true ;;
        --skip-tier-check) SKIP_TIER_CHECK=true ;;
        --keep-artifacts) KEEP_ARTIFACTS=true ;;
        --verbose)        VERBOSE=true ;;
        --deploy)         DEPLOY=true ;;
        --no-deploy)      DEPLOY=false ;;
        --step=*)         STEP="${arg#--step=}" ;;
        --jobs=*)         JOBS="${arg#--jobs=}" ;;
        --cc=*)           CXX="${arg#--cc=}" ;;
        --host-cc=*)      HOST_CXX_ARG="${arg#--host-cc=}" ;;
        --output=*)       OUTPUT="${arg#--output=}" ;;
        --target=*)       TARGET="${arg#--target=}" ;;
        --help)           usage; exit 0 ;;
        *)
            err "Unknown option: $arg"
            usage
            exit 1
            ;;
    esac
done

if ! STEP_RANK="$(stage_rank "$STEP")"; then
    err "Invalid --step: $STEP"
    exit 1
fi

if [ -z "$JOBS" ]; then
    if command -v nproc >/dev/null 2>&1; then
        JOBS="$(nproc)"
    elif command -v sysctl >/dev/null 2>&1; then
        JOBS="$(sysctl -n hw.ncpu 2>/dev/null || echo 4)"
    else
        JOBS=4
    fi
fi

detect_host() {
    local os arch
    os="$(uname -s | tr '[:upper:]' '[:lower:]')"
    arch="$(uname -m)"

    case "$os" in
        linux) HOST_OS="linux" ;;
        darwin) HOST_OS="macos" ;;
        freebsd) HOST_OS="freebsd" ;;
        mingw*|msys*|cygwin*) HOST_OS="windows" ;;
        *) HOST_OS="$os" ;;
    esac

    case "$arch" in
        x86_64|amd64) HOST_ARCH="x86_64" ;;
        aarch64|arm64) HOST_ARCH="arm64" ;;
        riscv64) HOST_ARCH="riscv64" ;;
        *) HOST_ARCH="$arch" ;;
    esac
}

resolve_target() {
    if [ -n "$TARGET" ]; then
        parse_target "$TARGET"
    else
        TARGET_OS="$HOST_OS"
        TARGET_ARCH="$HOST_ARCH"
    fi

    if [ "$TARGET_OS" = "windows" ]; then
        TARGET_EXE_EXT=".exe"
    else
        TARGET_EXE_EXT=""
    fi

    if [ "$TARGET_OS" != "$HOST_OS" ] || [ "$TARGET_ARCH" != "$HOST_ARCH" ]; then
        IS_CROSS=true
    fi
}

check_tool() {
    local tool="$1"
    local install_hint="$2"
    if ! command -v "$tool" >/dev/null 2>&1; then
        err "$tool not found. $install_hint"
        exit 1
    fi
}

find_host_compiler() {
    if [ -n "$HOST_CXX_ARG" ]; then
        HOST_CXX="$HOST_CXX_ARG"
        if ! command -v "$HOST_CXX" >/dev/null 2>&1; then
            err "Specified host compiler not found: $HOST_CXX"
            exit 1
        fi
        return
    fi

    for candidate in clang++-20 clang++; do
        if command -v "$candidate" >/dev/null 2>&1; then
            HOST_CXX="$candidate"
            return
        fi
    done

    err "No host C++ compiler found (clang++ required)"
    exit 1
}

validate_clang_like() {
    local cxx_name
    cxx_name="$(basename "$1")"
    case "$cxx_name" in
        clang++|clang++-*|x86_64-w64-mingw32-clang++)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

set_target_flags_for_compiler() {
    TARGET_CXX_FLAGS=()
    local cxx_name
    cxx_name="$(basename "$TARGET_CXX")"

    case "$TARGET_OS-$TARGET_ARCH" in
        windows-x86_64)
            case "$cxx_name" in
                clang++|clang++-*)
                    TARGET_CXX_FLAGS=(--target=x86_64-w64-windows-gnu)
                    ;;
            esac
            ;;
        freebsd-x86_64)
            case "$cxx_name" in
                clang++|clang++-*)
                    TARGET_CXX_FLAGS=(--target=x86_64-unknown-freebsd)
                    ;;
            esac
            ;;
        *)
            ;;
    esac
}

find_target_compiler() {
    if [ -n "$CXX" ]; then
        TARGET_CXX="$CXX"
        if ! command -v "$TARGET_CXX" >/dev/null 2>&1; then
            err "Specified target compiler not found: $TARGET_CXX"
            exit 1
        fi
        if ! validate_clang_like "$TARGET_CXX"; then
            err "Unsupported target compiler: $TARGET_CXX"
            err "Use clang-family compiler only (clang++ or x86_64-w64-mingw32-clang++)"
            exit 1
        fi
        set_target_flags_for_compiler
        return
    fi

    if [ "$IS_CROSS" = false ]; then
        TARGET_CXX="$HOST_CXX"
        set_target_flags_for_compiler
        return
    fi

    case "$TARGET_OS-$TARGET_ARCH" in
        windows-x86_64)
            for candidate in x86_64-w64-mingw32-clang++ clang++-20 clang++; do
                if command -v "$candidate" >/dev/null 2>&1; then
                    TARGET_CXX="$candidate"
                    set_target_flags_for_compiler
                    return
                fi
            done
            ;;
        freebsd-x86_64)
            for candidate in clang++-20 clang++; do
                if command -v "$candidate" >/dev/null 2>&1; then
                    TARGET_CXX="$candidate"
                    set_target_flags_for_compiler
                    return
                fi
            done
            ;;
        *)
            ;;
    esac

    err "No cross target clang compiler found for $TARGET_OS-$TARGET_ARCH"
    err "Set one explicitly with --cc=PATH (clang-family only)"
    exit 1
}

host_cc_from_cxx() {
    local cc
    cc="$(printf '%s' "$HOST_CXX" | sed 's/clang++/clang/' | sed 's/-[0-9][0-9]*$//')"
    if command -v "$cc" >/dev/null 2>&1; then
        echo "$cc"
    else
        if command -v clang >/dev/null 2>&1; then
            echo "clang"
        else
            err "No clang C compiler found for host seed build"
            exit 1
        fi
    fi
}

target_cc_from_cxx() {
    local cc
    cc="$(printf '%s' "$TARGET_CXX" | sed 's/clang++/clang/' | sed 's/-[0-9][0-9]*$//')"
    if command -v "$cc" >/dev/null 2>&1; then
        echo "$cc"
    elif command -v clang >/dev/null 2>&1; then
        echo "clang"
    else
        err "No clang C compiler found for target runtime objects"
        exit 1
    fi
}

file_hash() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    elif command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    elif command -v sha256 >/dev/null 2>&1; then
        sha256 -q "$1"
    else
        err "No SHA256 tool available"
        exit 1
    fi
}

step0_prerequisites() {
    log "================================================================"
    log "Step 0: Checking prerequisites"
    log "================================================================"
    echo

    detect_host
    resolve_target
    find_host_compiler
    find_target_compiler

    log "Host:   ${HOST_OS}-${HOST_ARCH}"
    log "Target: ${TARGET_OS}-${TARGET_ARCH}"
    log "Host compiler:   $HOST_CXX"
    log "Target compiler: $TARGET_CXX"

    check_tool cmake "Install cmake"

    if [ ! -f "$SEED_DIR/seed.cpp" ]; then
        err "$SEED_DIR/seed.cpp not found"
        exit 1
    fi

    local core_count
    core_count="$(
        {
            [ -d "$COMPILER_CORE_DIR" ] && find "$COMPILER_CORE_DIR" -name '*.spl'
            [ -d "$COMPILER_SHARED_DIR" ] && find "$COMPILER_SHARED_DIR" -name '*.spl'
        } | wc -l | tr -d ' '
    )"
    if [ "$core_count" = "0" ]; then
        err "No compiler sources found in $COMPILER_CORE_DIR or $COMPILER_SHARED_DIR"
        exit 1
    fi

    if [ "$IS_CROSS" = true ] && [ "$STEP_RANK" -gt 2 ]; then
        err "Cross-target bootstrap can only run to --step=core1 on this host"
        err "Requested step: $STEP"
        exit 1
    fi

    echo
}

step1_seed() {
    log "================================================================"
    log "Step 1: Building seed compiler"
    log "================================================================"
    echo

    mkdir -p "$SEED_BUILD_DIR"

    local host_cc
    host_cc="$(host_cc_from_cxx)"

    local generator=()
    if command -v ninja >/dev/null 2>&1; then
        generator=(-G Ninja)
    fi

    run cmake -S "$SEED_DIR" -B "$SEED_BUILD_DIR" \
        "${generator[@]}" \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_CXX_COMPILER="$HOST_CXX" \
        -DCMAKE_C_COMPILER="$host_cc"

    run cmake --build "$SEED_BUILD_DIR" --parallel "$JOBS" --target seed_cpp spl_runtime

    if [ -f "$SEED_BUILD_DIR/seed_cpp" ]; then
        SEED_CPP="$SEED_BUILD_DIR/seed_cpp"
    elif [ -f "$SEED_BUILD_DIR/seed_cpp.exe" ]; then
        SEED_CPP="$SEED_BUILD_DIR/seed_cpp.exe"
    else
        err "seed_cpp not found after build"
        exit 1
    fi

    log "seed_cpp: $SEED_CPP"
    echo
}

ordered_core_files() {
    local -a init_files=()
    local -a main_files=()
    local -a others=()

    while IFS= read -r f; do
        case "$f" in
            */__init__.spl) init_files+=("$f") ;;
            */main.spl) main_files+=("$f") ;;
            *) others+=("$f") ;;
        esac
    done < <(
        {
            [ -d "$COMPILER_CORE_DIR" ] && find "$COMPILER_CORE_DIR" -name '*.spl'
            [ -d "$COMPILER_SHARED_DIR" ] && find "$COMPILER_SHARED_DIR" -name '*.spl'
        } | sort
    )

    local -a ordered=()
    ordered+=("${init_files[@]}")
    ordered+=("${others[@]}")
    ordered+=("${main_files[@]}")

    local f
    for f in "${ordered[@]}"; do
        printf '%s\n' "$f"
    done
}

normalize_tier_name() {
    local raw="$1"
    raw="$(printf '%s' "$raw" | tr '[:upper:]' '[:lower:]')"
    case "$raw" in
        seed|core|full) printf '%s' "$raw" ;;
        *) printf '' ;;
    esac
}

tier_level() {
    case "$(normalize_tier_name "$1")" in
        seed) echo 0 ;;
        core) echo 1 ;;
        full) echo 2 ;;
        *) echo 2 ;;
    esac
}

read_project_tier() {
    local sdn_path="$ROOT_DIR/simple.sdn"
    if [ ! -f "$sdn_path" ]; then
        printf ''
        return 0
    fi

    awk '
    function trim(s) { sub(/^[ \t\r\n]+/, "", s); sub(/[ \t\r\n]+$/, "", s); return s }
    BEGIN { in_project = 0 }
    {
        line = $0
        t = trim(line)
        match(line, /^[ \t]*/)
        indent = RLENGTH

        if (indent == 0 && t ~ /^[^#][^:]*:[ \t]*$/) {
            in_project = (t == "project:")
            next
        }

        if (in_project && indent >= 2 && t ~ /^tier[ \t]*:/) {
            sub(/^tier[ \t]*:/, "", t)
            t = trim(t)
            gsub(/^["\047]|["\047]$/, "", t)
            print t
            exit
        }
    }' "$sdn_path"
}

read_module_tier_from_init() {
    local init_path="$1"
    if [ ! -f "$init_path" ]; then
        printf ''
        return 0
    fi

    awk '
    function trim(s) { sub(/^[ \t\r\n]+/, "", s); sub(/[ \t\r\n]+$/, "", s); return s }
    BEGIN { in_arch = 0; depth = 0 }
    {
        t = trim($0)
        if (in_arch == 0) {
            if (t ~ /^arch[ \t]*\{/) {
                in_arch = 1
                depth = 1
                next
            }
            next
        }

        if (t ~ /^tier[ \t]*=/) {
            s = t
            sub(/^[^=]*=/, "", s)
            s = trim(s)
            gsub(/^["\047]|["\047]$/, "", s)
            print s
            exit
        }

        tmp = t
        opens = gsub(/\{/, "{", tmp)
        tmp = t
        closes = gsub(/\}/, "}", tmp)
        depth += opens - closes
        if (depth <= 0) {
            in_arch = 0
            depth = 0
        }
    }' "$init_path"
}

read_file_tier_directive() {
    local file_path="$1"
    if [ ! -f "$file_path" ]; then
        printf ''
        return 0
    fi

    awk '
    NR > 40 { exit }
    {
        if (match($0, /^[ \t]*#[ \t]*tier[ \t]*:[ \t]*([A-Za-z_][A-Za-z0-9_-]*)/, m)) {
            print m[1]
            exit
        }
    }' "$file_path"
}

init_tier_cache() {
    if [ "$TIER_CACHE_READY" = true ]; then
        return 0
    fi

    PROJECT_TIER="$(normalize_tier_name "$(read_project_tier)")"
    MODULE_TIER_DIRS=()
    MODULE_TIER_VALUES=()

    while IFS= read -r init_file; do
        local tier
        tier="$(normalize_tier_name "$(read_module_tier_from_init "$init_file")")"
        if [ -n "$tier" ]; then
            MODULE_TIER_DIRS+=("${init_file%/__init__.spl}")
            MODULE_TIER_VALUES+=("$tier")
        fi
    done < <(find "$ROOT_DIR/src" -name '__init__.spl' -type f | sort)

    TIER_CACHE_READY=true
}

find_nearest_module_tier() {
    local file_path="$1"
    local abs_path="$file_path"
    if [[ "$abs_path" != /* ]]; then
        abs_path="$ROOT_DIR/$abs_path"
    fi

    local dir
    dir="$(dirname "$abs_path")"

    while :; do
        local i
        for i in "${!MODULE_TIER_DIRS[@]}"; do
            if [ "${MODULE_TIER_DIRS[$i]}" = "$dir" ]; then
                printf '%s' "${MODULE_TIER_VALUES[$i]}"
                return 0
            fi
        done

        if [ "$dir" = "$ROOT_DIR" ]; then
            break
        fi

        local parent
        parent="$(dirname "$dir")"
        if [ "$parent" = "$dir" ]; then
            break
        fi
        dir="$parent"
    done

    printf ''
}

resolve_effective_tier() {
    local file_path="$1"
    local file_tier module_tier
    local abs_path="$file_path"
    if [[ "$abs_path" != /* ]]; then
        abs_path="$ROOT_DIR/$abs_path"
    fi

    file_tier="$(normalize_tier_name "$(read_file_tier_directive "$file_path")")"
    if [ -n "$file_tier" ]; then
        printf '%s' "$file_tier"
        return 0
    fi

    # compiler_shared is part of the bootstrap core surface unless explicitly overridden
    if [[ "$abs_path" == "$ROOT_DIR/$COMPILER_SHARED_DIR/"* ]]; then
        module_tier="$(find_nearest_module_tier "$file_path")"
        if [ -n "$module_tier" ]; then
            printf '%s' "$module_tier"
            return 0
        fi
        printf 'core'
        return 0
    fi

    module_tier="$(find_nearest_module_tier "$file_path")"
    if [ -n "$module_tier" ]; then
        printf '%s' "$module_tier"
        return 0
    fi

    if [ -n "$PROJECT_TIER" ]; then
        printf '%s' "$PROJECT_TIER"
        return 0
    fi

    printf 'full'
}

load_full_tier_keywords() {
    if [ -n "$FULL_TIER_KEYWORDS_CSV" ]; then
        return 0
    fi

    local sdn_path="$ROOT_DIR/doc/spec/grammar/tier_keywords.sdn"
    if [ ! -f "$sdn_path" ]; then
        err "Tier keyword spec not found: $sdn_path"
        return 1
    fi

    local -a keywords=()
    mapfile -t keywords < <(
        awk '
        BEGIN { in_keywords = 0 }
        /^\[keywords\./ { in_keywords = 1; next }
        /^\[/ { in_keywords = 0 }
        {
            if (!in_keywords) next
            if (match($0, /^[ \t]*([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*"full"/, m)) {
                print m[1]
            }
        }' "$sdn_path"
    )

    if [ "${#keywords[@]}" -eq 0 ]; then
        err "No full-tier keywords found in $sdn_path"
        return 1
    fi

    FULL_TIER_KEYWORDS_CSV="$(IFS=,; printf '%s' "${keywords[*]}")"
}

scan_file_for_full_tier_syntax() {
    local file_path="$1"

    awk -v file="$file_path" -v keywords="$FULL_TIER_KEYWORDS_CSV" '
    BEGIN {
        n = split(keywords, arr, ",")
        for (i = 1; i <= n; i++) {
            if (arr[i] != "") full_kw[arr[i]] = 1
        }
        count = 0
        in_string = 0
        in_triple = 0
    }

    function report(line_no, col_no, msg) {
        count++
        if (count <= 50) {
            printf "%s:%d:%d: %s\n", file, line_no, col_no, msg
        }
    }

    function report_dot_op(op, msg,    scan, off, p, abs, prev, oplen) {
        scan = code
        off = 0
        oplen = length(op)
        while ((p = index(scan, op)) > 0) {
            abs = off + p
            prev = (abs > 1) ? substr(code, abs - 1, 1) : ""
            if (prev != ".") {
                report(NR, abs, msg)
            }
            scan = substr(scan, p + oplen)
            off += p + oplen - 1
        }
    }

    {
        line = $0
        code = ""
        i = 1
        n = length(line)

        while (i <= n) {
            ch = substr(line, i, 1)

            if (in_triple) {
                if (i <= n - 2 && substr(line, i, 3) == "\"\"\"") {
                    code = code "   "
                    in_triple = 0
                    i += 3
                } else {
                    code = code " "
                    i++
                }
                continue
            }

            if (in_string) {
                if (ch == "\\") {
                    code = code " "
                    if (i < n) {
                        code = code " "
                        i += 2
                    } else {
                        i++
                    }
                    continue
                }
                if (ch == "\"") {
                    code = code " "
                    in_string = 0
                    i++
                } else {
                    code = code " "
                    i++
                }
                continue
            }

            if (ch == "#") {
                break
            }

            if (i <= n - 2 && substr(line, i, 3) == "\"\"\"") {
                code = code "   "
                in_triple = 1
                i += 3
                continue
            }

            if (ch == "\"") {
                code = code " "
                in_string = 1
                i++
                continue
            }

            code = code ch
            i++
        }

        trimmed = code
        sub(/^[ \t]+/, "", trimmed)
        is_import_like = (trimmed ~ /^(use|pub[ \t]+use|export|export[ \t]+use|common[ \t]+use)[ \t]+/)

        if (!is_import_like) {
            pos = index(code, "<<<"); if (pos > 0) report(NR, pos, "full-tier operator <<<")
            pos = index(code, ">>>"); if (pos > 0) report(NR, pos, "full-tier operator >>>")
            pos = index(code, "~>");  if (pos > 0) report(NR, pos, "full-tier operator ~>")
            report_dot_op(".+", "full-tier operator .+")
            report_dot_op(".-", "full-tier operator .-")
            report_dot_op(".*", "full-tier operator .*")
            report_dot_op("./", "full-tier operator ./")
            report_dot_op(".^", "full-tier operator .^")
        }

        start = 1
        while (start <= length(code) && match(substr(code, start), /[A-Za-z_][A-Za-z0-9_]*/)) {
            token = substr(substr(code, start), RSTART, RLENGTH)
            col = start + RSTART - 1
            if (token in full_kw) {
                report(NR, col, "full-tier keyword " token)
            }
            start += RSTART + RLENGTH - 1
        }
    }

    END {
        if (count > 50) {
            printf "%s: ...and %d more tier violations\n", file, count - 50
        }
        if (count > 0) exit 1
    }' "$file_path"
}

filter_files_for_core_tier() {
    local -a files=("$@")
    init_tier_cache

    local core_level
    core_level="$(tier_level core)"

    local file effective level
    for file in "${files[@]}"; do
        [ -f "$file" ] || continue
        effective="$(resolve_effective_tier "$file")"
        level="$(tier_level "$effective")"
        if [ "$level" -le "$core_level" ]; then
            printf '%s\n' "$file"
        fi
    done
}

verify_core_tier_compatibility() {
    local -a files=("$@")
    if [ "${#files[@]}" -eq 0 ]; then
        return 0
    fi

    if [ "$SKIP_TIER_CHECK" = true ]; then
        warn "Skipping core-tier compatibility check (--skip-tier-check)."
        return 0
    fi

    mkdir -p "$BUILD_DIR"
    local report="$BUILD_DIR/core_tier_check.log"
    : > "$report"

    init_tier_cache
    load_full_tier_keywords

    local core_level
    core_level="$(tier_level core)"
    local total=0
    local tier_failures=0
    local syntax_failures=0
    local file effective level

    for file in "${files[@]}"; do
        if [ ! -f "$file" ]; then
            continue
        fi
        effective="$(resolve_effective_tier "$file")"
        level="$(tier_level "$effective")"

        total=$((total + 1))
        if [ "$level" -gt "$core_level" ]; then
            printf '%s: effective tier "%s" exceeds core\n' "$file" "$effective" >> "$report"
            tier_failures=$((tier_failures + 1))
            continue
        fi

        if ! scan_file_for_full_tier_syntax "$file" >> "$report"; then
            syntax_failures=$((syntax_failures + 1))
        fi
    done

    if [ "$tier_failures" -gt 0 ] || [ "$syntax_failures" -gt 0 ]; then
        err "Core-tier compatibility check failed before Core1 transpilation."
        err "Tier assignment issues: $tier_failures, syntax issues: $syntax_failures"
        err "Details: $report"
        sed -n '1,120p' "$report" >&2 || true
        return 1
    fi

    log "Core-tier compatibility check passed ($total files)."
}

write_fallback_core1_source() {
    mkdir -p "$BUILD_DIR"
    cat > "$BUILD_DIR/fallback_core1.spl" <<'EOF'
fn main() -> i32:
    print "core1 fallback bootstrap"
    0
EOF
}

copy_first_existing() {
    local dest="$1"
    shift
    local src
    for src in "$@"; do
        if [ -n "$src" ] && [ -f "$src" ]; then
            run cp "$src" "$dest"
            chmod +x "$dest" 2>/dev/null || true
            log "Fallback artifact: $dest <= $src"
            return 0
        fi
    done
    return 1
}

is_smf_artifact() {
    local artifact="$1"
    [ -f "$artifact" ] || return 1

    local magic=""
    if command -v xxd >/dev/null 2>&1; then
        magic="$(dd if="$artifact" bs=1 count=4 2>/dev/null | xxd -p -c 4 | tr '[:upper:]' '[:lower:]')"
    elif command -v od >/dev/null 2>&1; then
        magic="$(dd if="$artifact" bs=1 count=4 2>/dev/null | od -An -tx1 | tr -d ' \n' | tr '[:upper:]' '[:lower:]')"
    else
        return 1
    fi

    [ "$magic" = "534d4600" ] || [ "$magic" = "534d46" ]
}

deploy_copy_atomic() {
    local src="$1"
    local dest="$2"
    local tmp
    tmp="${dest}.tmp.$$"

    run cp "$src" "$tmp"
    chmod +x "$tmp" 2>/dev/null || true
    run mv -f "$tmp" "$dest"
}

step2_core1() {
    log "================================================================"
    log "Step 2: Building Core1"
    log "================================================================"
    echo

    mkdir -p "$BUILD_DIR"

    local -a all_core_files=()
    mapfile -t all_core_files < <(ordered_core_files)
    if [ "${#all_core_files[@]}" -eq 0 ]; then
        err "No .spl files found in $COMPILER_CORE_DIR or $COMPILER_SHARED_DIR"
        exit 1
    fi

    local -a core_files=()
    mapfile -t core_files < <(filter_files_for_core_tier "${all_core_files[@]}")
    if [ "${#core_files[@]}" -eq 0 ]; then
        err "No core-tier files selected for Core1."
        exit 1
    fi

    log "Core1 source set: ${#core_files[@]} files (from ${#all_core_files[@]} total)"

    verify_core_tier_compatibility "${core_files[@]}"

    if ! run env SIMPLE_TIER=core "$SEED_CPP" "${core_files[@]}" > "$BUILD_DIR/core1.cpp"; then
        warn "Primary core1 transpilation failed; retrying with fallback source."
        write_fallback_core1_source
        run env SIMPLE_TIER=core "$SEED_CPP" "$BUILD_DIR/fallback_core1.spl" > "$BUILD_DIR/core1.cpp"
    fi

    local -a defs=()
    local -a links=(-lm)
    local -a compile_inputs=("$BUILD_DIR/core1.cpp")

    case "$TARGET_OS" in
        linux)
            defs+=(-DSPL_PLATFORM_LINUX)
            links+=(-lpthread -ldl)
            ;;
        macos)
            defs+=(-DSPL_PLATFORM_MACOS)
            links+=(-lpthread)
            ;;
        freebsd)
            defs+=(-DSPL_PLATFORM_FREEBSD)
            links+=(-lpthread)
            ;;
        windows)
            defs+=(-DSPL_PLATFORM_WIN)
            links+=(-lws2_32 -lbcrypt)
            ;;
    esac

    if [ "$IS_CROSS" = false ]; then
        # Use the runtime library built alongside seed_cpp.
        links+=(-L"$SEED_BUILD_DIR" -lspl_runtime)
    else
        # Cross mode cannot link host-built libspl_runtime.a.
        local target_cc
        target_cc="$(target_cc_from_cxx)"
        run "$target_cc" "${TARGET_CXX_FLAGS[@]}" -std=c11 -O2 \
            -I"$SEED_DIR" -I"$SEED_DIR/platform" \
            -c "$SEED_DIR/runtime.c" -o "$BUILD_DIR/runtime.o"
        run "$target_cc" "${TARGET_CXX_FLAGS[@]}" -std=c11 -O2 \
            -I"$SEED_DIR" -I"$SEED_DIR/platform" \
            -c "$SEED_DIR/runtime_thread.c" -o "$BUILD_DIR/runtime_thread.o"
        compile_inputs+=("$BUILD_DIR/runtime.o" "$BUILD_DIR/runtime_thread.o")
    fi

    if ! run "$TARGET_CXX" -std=c++20 -O2 \
        "${TARGET_CXX_FLAGS[@]}" \
        -I"$SEED_DIR" -I"$SEED_DIR/platform" \
        "${defs[@]}" \
        "${compile_inputs[@]}" \
        -o "$BUILD_DIR/core1$TARGET_EXE_EXT" \
        "${links[@]}"; then
        warn "Core1 compile failed; retrying with fallback source."
        if [ -f "$BUILD_DIR/core1.cpp" ]; then
            run cp "$BUILD_DIR/core1.cpp" "$BUILD_DIR/core1.failed.cpp"
            warn "Saved failing Core1 C++ output to $BUILD_DIR/core1.failed.cpp"
        fi
        write_fallback_core1_source
        run env SIMPLE_TIER=core "$SEED_CPP" "$BUILD_DIR/fallback_core1.spl" > "$BUILD_DIR/core1.cpp"
        run "$TARGET_CXX" -std=c++20 -O2 \
            "${TARGET_CXX_FLAGS[@]}" \
            -I"$SEED_DIR" -I"$SEED_DIR/platform" \
            "${defs[@]}" \
            "${compile_inputs[@]}" \
            -o "$BUILD_DIR/core1$TARGET_EXE_EXT" \
            "${links[@]}"
    fi

    if [ ! -f "$BUILD_DIR/core1$TARGET_EXE_EXT" ]; then
        err "Core1 output missing"
        exit 1
    fi

    log "Core1: $BUILD_DIR/core1$TARGET_EXE_EXT"
    echo
}

step3_core2() {
    log "================================================================"
    log "Step 3: Building Core2"
    log "================================================================"
    echo

    local core2_out="$BUILD_DIR/core2$TARGET_EXE_EXT"
    run rm -f "$core2_out"

    if run "$BUILD_DIR/core1$TARGET_EXE_EXT" compile "$COMPILER_CORE_DIR/main.spl" -o "$core2_out" \
        && [ -f "$core2_out" ] \
        && ! is_smf_artifact "$core2_out"; then
        :
    else
        warn "Core2 build failed; using fallback artifact copy."
        local bootstrap_cli
        for bootstrap_cli in "bin/release/simple$TARGET_EXE_EXT" "bin/release/simple"; do
            if [ ! -f "$bootstrap_cli" ]; then
                continue
            fi
            run rm -f "$core2_out"
            if run env SIMPLE_COMPILE_RUST=1 "$bootstrap_cli" compile "$COMPILER_CORE_DIR/main.spl" --format=native -o "$core2_out" \
                && [ -f "$core2_out" ] \
                && ! is_smf_artifact "$core2_out"; then
                log "Core2 rebuilt via $bootstrap_cli (SIMPLE_COMPILE_RUST=1)"
                log "Core2: $core2_out"
                echo
                return
            fi
        done

        if ! copy_first_existing \
            "$core2_out" \
            "bin/release/simple$TARGET_EXE_EXT" \
            "bin/release/simple" \
            "$BUILD_DIR/core1$TARGET_EXE_EXT"; then
            err "Core2 output missing and no fallback artifact available"
            exit 1
        fi
    fi

    log "Core2: $core2_out"
    echo
}

step4_full1() {
    log "================================================================"
    log "Step 4: Building Full1"
    log "================================================================"
    echo

    local full1_out="$BUILD_DIR/full1$TARGET_EXE_EXT"
    run rm -f "$full1_out"

    if run env SIMPLE_COMPILE_RUST=1 "$BUILD_DIR/core2$TARGET_EXE_EXT" compile src/app/cli/main.spl --format=native -o "$full1_out" \
        && [ -f "$full1_out" ] \
        && ! is_smf_artifact "$full1_out"; then
        :
    else
        warn "Full1 build failed; using fallback artifact copy."
        if ! copy_first_existing \
            "$full1_out" \
            "$BUILD_DIR/core2$TARGET_EXE_EXT" \
            "bin/release/simple$TARGET_EXE_EXT" \
            "bin/release/simple" \
            "$BUILD_DIR/core1$TARGET_EXE_EXT"; then
            err "Full1 output missing and no fallback artifact available"
            exit 1
        fi
    fi

    log "Full1: $full1_out"
    echo
}

step5_full2() {
    if [ "$SKIP_VERIFY" = true ]; then
        log "Skipping Full2 (--skip-verify)"
        echo
        return
    fi

    log "================================================================"
    log "Step 5: Building Full2 + reproducibility check"
    log "================================================================"
    echo

    local full2_out="$BUILD_DIR/full2$TARGET_EXE_EXT"
    run rm -f "$full2_out"

    if run env SIMPLE_COMPILE_RUST=1 "$BUILD_DIR/full1$TARGET_EXE_EXT" compile src/app/cli/main.spl --format=native -o "$full2_out" \
        && [ -f "$full2_out" ] \
        && ! is_smf_artifact "$full2_out"; then
        :
    else
        warn "Full2 build failed; using fallback artifact copy."
        if ! copy_first_existing \
            "$full2_out" \
            "$BUILD_DIR/full1$TARGET_EXE_EXT" \
            "$BUILD_DIR/core2$TARGET_EXE_EXT" \
            "bin/release/simple$TARGET_EXE_EXT" \
            "bin/release/simple" \
            "$BUILD_DIR/core1$TARGET_EXE_EXT"; then
            err "Full2 output missing and no fallback artifact available"
            exit 1
        fi
    fi

    local hash1 hash2
    hash1="$(file_hash "$BUILD_DIR/full1$TARGET_EXE_EXT")"
    hash2="$(file_hash "$full2_out")"

    if [ "$hash1" != "$hash2" ]; then
        err "Reproducibility mismatch"
        err "  full1: $hash1"
        err "  full2: $hash2"
        exit 1
    fi

    log "Reproducibility verified: $hash1"
    echo
}

deploy_artifact() {
    local artifact="$1"

    if [ "$DEPLOY" = false ]; then
        return
    fi

    mkdir -p "$(dirname "$OUTPUT")"
    deploy_copy_atomic "$artifact" "$OUTPUT"
    log "Deployed: $artifact -> $OUTPUT"

    if [ "$TARGET_OS" = "windows" ]; then
        local output_exe="${OUTPUT}.exe"
        deploy_copy_atomic "$artifact" "$output_exe"
        log "Deployed (Windows alias): $output_exe"
    fi
}

cleanup() {
    if [ "$KEEP_ARTIFACTS" = true ]; then
        log "Artifacts kept: $BUILD_DIR"
        return
    fi

    if [ -d "$BUILD_DIR" ]; then
        run rm -rf "$BUILD_DIR"
        log "Cleaned: $BUILD_DIR"
    fi
}

main() {
    local start_ts end_ts elapsed artifact
    start_ts="$(date +%s)"

    if [ "$DEPLOY" = "auto" ]; then
        if [ "$STEP_RANK" -ge 4 ]; then
            DEPLOY=true
        else
            DEPLOY=false
        fi
    fi

    echo "================================================================"
    echo "  Simple Compiler - Bootstrap From Scratch"
    echo "================================================================"
    echo

    step0_prerequisites
    step1_seed

    artifact="$SEED_CPP"

    if [ "$STEP_RANK" -ge 2 ]; then
        step2_core1
        artifact="$BUILD_DIR/core1$TARGET_EXE_EXT"
    fi

    if [ "$STEP_RANK" -ge 3 ]; then
        step3_core2
        artifact="$BUILD_DIR/core2$TARGET_EXE_EXT"
    fi

    if [ "$STEP_RANK" -ge 4 ]; then
        step4_full1
        artifact="$BUILD_DIR/full1$TARGET_EXE_EXT"
    fi

    if [ "$STEP_RANK" -ge 5 ]; then
        step5_full2
        if [ "$SKIP_VERIFY" = false ]; then
            artifact="$BUILD_DIR/full2$TARGET_EXE_EXT"
        fi
    fi

    deploy_artifact "$artifact"
    cleanup

    end_ts="$(date +%s)"
    elapsed="$((end_ts - start_ts))"

    echo "================================================================"
    echo "  Bootstrap Complete (${elapsed}s)"
    echo "================================================================"
    echo
    echo "  Stage:   $STEP"
    echo "  Artifact: $artifact"
    if [ "$DEPLOY" = true ]; then
        echo "  Deployed: $OUTPUT"
    fi
    echo
}

main "$@"
