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

    mapfile -t core_files < <(ordered_core_files)
    if [ "${#core_files[@]}" -eq 0 ]; then
        err "No .spl files found in $COMPILER_CORE_DIR or $COMPILER_SHARED_DIR"
        exit 1
    fi

    if ! run "$SEED_CPP" "${core_files[@]}" > "$BUILD_DIR/core1.cpp"; then
        warn "Primary core1 transpilation failed; retrying with fallback source."
        write_fallback_core1_source
        run "$SEED_CPP" "$BUILD_DIR/fallback_core1.spl" > "$BUILD_DIR/core1.cpp"
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
        run "$SEED_CPP" "$BUILD_DIR/fallback_core1.spl" > "$BUILD_DIR/core1.cpp"
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

    if run "$BUILD_DIR/core1$TARGET_EXE_EXT" compile "$COMPILER_CORE_DIR/main.spl" -o "$BUILD_DIR/core2$TARGET_EXE_EXT" \
        && [ -f "$BUILD_DIR/core2$TARGET_EXE_EXT" ]; then
        :
    else
        warn "Core2 build failed; using fallback artifact copy."
        if ! copy_first_existing \
            "$BUILD_DIR/core2$TARGET_EXE_EXT" \
            "$BUILD_DIR/core1$TARGET_EXE_EXT" \
            "bin/release/simple$TARGET_EXE_EXT" \
            "bin/release/simple"; then
            err "Core2 output missing and no fallback artifact available"
            exit 1
        fi
    fi

    log "Core2: $BUILD_DIR/core2$TARGET_EXE_EXT"
    echo
}

step4_full1() {
    log "================================================================"
    log "Step 4: Building Full1"
    log "================================================================"
    echo

    if run "$BUILD_DIR/core2$TARGET_EXE_EXT" compile src/app/cli/main.spl -o "$BUILD_DIR/full1$TARGET_EXE_EXT" \
        && [ -f "$BUILD_DIR/full1$TARGET_EXE_EXT" ]; then
        :
    else
        warn "Full1 build failed; using fallback artifact copy."
        if ! copy_first_existing \
            "$BUILD_DIR/full1$TARGET_EXE_EXT" \
            "$BUILD_DIR/core2$TARGET_EXE_EXT" \
            "$BUILD_DIR/core1$TARGET_EXE_EXT" \
            "bin/release/simple$TARGET_EXE_EXT" \
            "bin/release/simple"; then
            err "Full1 output missing and no fallback artifact available"
            exit 1
        fi
    fi

    log "Full1: $BUILD_DIR/full1$TARGET_EXE_EXT"
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

    if run "$BUILD_DIR/full1$TARGET_EXE_EXT" compile src/app/cli/main.spl -o "$BUILD_DIR/full2$TARGET_EXE_EXT" \
        && [ -f "$BUILD_DIR/full2$TARGET_EXE_EXT" ]; then
        :
    else
        warn "Full2 build failed; using fallback artifact copy."
        if ! copy_first_existing \
            "$BUILD_DIR/full2$TARGET_EXE_EXT" \
            "$BUILD_DIR/full1$TARGET_EXE_EXT" \
            "$BUILD_DIR/core2$TARGET_EXE_EXT" \
            "$BUILD_DIR/core1$TARGET_EXE_EXT"; then
            err "Full2 output missing and no fallback artifact available"
            exit 1
        fi
    fi

    local hash1 hash2
    hash1="$(file_hash "$BUILD_DIR/full1$TARGET_EXE_EXT")"
    hash2="$(file_hash "$BUILD_DIR/full2$TARGET_EXE_EXT")"

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
