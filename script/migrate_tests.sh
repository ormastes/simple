#!/bin/bash
# Test Directory Migration Script
# Moves test files from old layout to new layout
# Phase 2 of test refactoring plan
set -euo pipefail

ROOT="/home/ormastes/dev/pub/simple"
cd "$ROOT"

echo "=== Phase 2: Test Directory Migration ==="
echo ""

# =========================================================================
# Step 1: Create new directory structure
# =========================================================================
echo "Step 1: Creating new directory structure..."

mkdir -p test/unit/std
mkdir -p test/unit/lib/database
mkdir -p test/unit/lib/pure
mkdir -p test/unit/lib/collections
mkdir -p test/unit/app/build
mkdir -p test/unit/app/cli
mkdir -p test/unit/app/desugar
mkdir -p test/unit/app/formatter
mkdir -p test/unit/app/linter
mkdir -p test/unit/app/io
mkdir -p test/unit/app/mcp
mkdir -p test/unit/app/test_runner
mkdir -p test/unit/app/duplicate_check
mkdir -p test/unit/app/fix
mkdir -p test/unit/app/package
mkdir -p test/unit/app/interpreter
mkdir -p test/unit/app/diagnostics
mkdir -p test/unit/app/utils
mkdir -p test/unit/app/devtools
mkdir -p test/unit/app/linker_gen
mkdir -p test/unit/compiler/codegen
mkdir -p test/unit/compiler/linker
mkdir -p test/unit/compiler/regalloc
mkdir -p test/unit/compiler/parser
mkdir -p test/unit/compiler/backend
mkdir -p test/unit/compiler/blocks
mkdir -p test/unit/compiler/config
mkdir -p test/unit/compiler/dependency
mkdir -p test/feature
mkdir -p test/integration/spec
mkdir -p test/system/compiler
mkdir -p test/system/interpreter/sample/python_inspired_sample
mkdir -p test/system/platform
mkdir -p test/system/dap
mkdir -p test/system/watcher
mkdir -p test/system/ffi
mkdir -p test/benchmark
mkdir -p test/fixtures/sample_programs

echo "  Created directory structure."

# =========================================================================
# Step 2: Move feature specs (test/system/features/* → test/feature/)
# =========================================================================
echo "Step 2: Moving feature specs..."

feat_count=0
for dir in test/system/features/*/; do
    if [ -d "$dir" ]; then
        for f in "$dir"*.spl; do
            if [ -f "$f" ]; then
                basename_f=$(basename "$f")
                if [ ! -f "test/feature/$basename_f" ]; then
                    cp "$f" "test/feature/$basename_f"
                    feat_count=$((feat_count + 1))
                fi
            fi
        done
    fi
done
# Also move top-level feature specs
for f in test/system/features/*_spec.spl; do
    if [ -f "$f" ]; then
        basename_f=$(basename "$f")
        if [ ! -f "test/feature/$basename_f" ]; then
            cp "$f" "test/feature/$basename_f"
            feat_count=$((feat_count + 1))
        fi
    fi
done
echo "  Moved $feat_count feature specs to test/feature/"

# =========================================================================
# Step 3: Move unit tests (test/lib/std/unit/core/* → test/unit/std/)
# =========================================================================
echo "Step 3: Moving stdlib unit tests..."

std_count=0
for f in test/lib/std/unit/core/*_spec.spl test/lib/std/unit/core/*_test.spl; do
    if [ -f "$f" ]; then
        basename_f=$(basename "$f")
        if [ ! -f "test/unit/std/$basename_f" ]; then
            cp "$f" "test/unit/std/$basename_f"
            std_count=$((std_count + 1))
        fi
    fi
done
# Move test/std/* as well
for f in test/std/*_spec.spl test/std/*_test.spl; do
    if [ -f "$f" ]; then
        basename_f=$(basename "$f")
        if [ ! -f "test/unit/std/$basename_f" ]; then
            cp "$f" "test/unit/std/$basename_f"
            std_count=$((std_count + 1))
        fi
    fi
done
echo "  Moved $std_count stdlib unit tests to test/unit/std/"

# =========================================================================
# Step 4: Move app tests (test/app/* → test/unit/app/**)
# =========================================================================
echo "Step 4: Moving app tests..."

app_count=0

# Build tests
for f in test/app/build/*_spec.spl test/build/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/build/$bn" ]; then
            cp "$f" "test/unit/app/build/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Formatter tests
for f in test/app/formatter*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/formatter/$bn" ]; then
            cp "$f" "test/unit/app/formatter/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# MCP tests
for f in test/app/mcp/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/mcp/$bn" ]; then
            cp "$f" "test/unit/app/mcp/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# IO tests
for f in test/app/io/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/io/$bn" ]; then
            cp "$f" "test/unit/app/io/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Duplicate check tests
for f in test/app/duplicate_check/*_spec.spl test/app/duplicate_check_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/duplicate_check/$bn" ]; then
            cp "$f" "test/unit/app/duplicate_check/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Package tests
for f in test/app/package/*_spec.spl test/app/package/registry/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/package/$bn" ]; then
            cp "$f" "test/unit/app/package/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Interpreter tests
for f in test/app/interpreter/*/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/interpreter/$bn" ]; then
            cp "$f" "test/unit/app/interpreter/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Test runner tests
for f in test/app/test_runner/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/test_runner/$bn" ]; then
            cp "$f" "test/unit/app/test_runner/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Utils tests
for f in test/app/utils/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/utils/$bn" ]; then
            cp "$f" "test/unit/app/utils/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Linker gen tests
for f in test/app/linker_gen/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/linker_gen/$bn" ]; then
            cp "$f" "test/unit/app/linker_gen/$bn"
            app_count=$((app_count + 1))
        fi
    fi
done

# Top-level app tests (dap, devtools, etc.)
for f in test/app/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        # Route to appropriate subdirectory
        case "$bn" in
            dap_spec.spl) dest="test/system/dap/$bn" ;;
            devtools*) dest="test/unit/app/devtools/$bn" ;;
            *) dest="test/unit/app/$bn" ;;
        esac
        dir=$(dirname "$dest")
        mkdir -p "$dir"
        if [ ! -f "$dest" ]; then
            cp "$f" "$dest"
            app_count=$((app_count + 1))
        fi
    fi
done

echo "  Moved $app_count app tests"

# =========================================================================
# Step 5: Move compiler tests
# =========================================================================
echo "Step 5: Moving compiler tests..."

comp_count=0

# Backend tests
for f in test/compiler/backend/*_spec.spl test/compiler/backend/common/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/compiler/backend/$bn" ]; then
            cp "$f" "test/unit/compiler/backend/$bn"
            comp_count=$((comp_count + 1))
        fi
    fi
done

# Blocks tests
for f in test/compiler/blocks/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/compiler/blocks/$bn" ]; then
            cp "$f" "test/unit/compiler/blocks/$bn"
            comp_count=$((comp_count + 1))
        fi
    fi
done

# Config tests
for f in test/compiler/config/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/compiler/config/$bn" ]; then
            cp "$f" "test/unit/compiler/config/$bn"
            comp_count=$((comp_count + 1))
        fi
    fi
done

# Dependency tests
for f in test/compiler/dependency/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/compiler/dependency/$bn" ]; then
            cp "$f" "test/unit/compiler/dependency/$bn"
            comp_count=$((comp_count + 1))
        fi
    fi
done

# Top-level compiler tests
for f in test/compiler/*_spec.spl test/compiler/*_test.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/compiler/$bn" ]; then
            cp "$f" "test/unit/compiler/$bn"
            comp_count=$((comp_count + 1))
        fi
    fi
done

# Compiler specs from src/
for f in src/compiler/linker/test/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/compiler/linker/$bn" ]; then
            cp "$f" "test/unit/compiler/linker/$bn"
            comp_count=$((comp_count + 1))
        fi
    fi
done

echo "  Moved $comp_count compiler tests"

# =========================================================================
# Step 6: Move database/library tests
# =========================================================================
echo "Step 6: Moving library tests..."

lib_count=0

# Database tests from test/lib/
for f in test/lib/database*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/lib/database/$bn" ]; then
            cp "$f" "test/unit/lib/database/$bn"
            lib_count=$((lib_count + 1))
        fi
    fi
done

# Database tests from test/integration/
for f in test/integration/database*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/lib/database/$bn" ]; then
            cp "$f" "test/unit/lib/database/$bn"
            lib_count=$((lib_count + 1))
        fi
    fi
done

# Pure/ML tests from src/
for f in src/lib/pure/test/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/lib/pure/$bn" ]; then
            cp "$f" "test/unit/lib/pure/$bn"
            lib_count=$((lib_count + 1))
        fi
    fi
done

# Collections tests
for f in test/lib/collections/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/lib/collections/$bn" ]; then
            cp "$f" "test/unit/lib/collections/$bn"
            lib_count=$((lib_count + 1))
        fi
    fi
done

echo "  Moved $lib_count library tests"

# =========================================================================
# Step 7: Move integration tests
# =========================================================================
echo "Step 7: Moving integration tests..."

int_count=0
for f in test/integration/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        # Skip database ones (already moved)
        case "$bn" in
            database*) continue ;;
        esac
        if [ ! -f "test/integration/$bn" ]; then
            # Already in correct place
            :
        fi
        int_count=$((int_count + 1))
    fi
done
# Move integration/spec/ contents
for f in test/integration/spec/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/integration/$bn" ]; then
            cp "$f" "test/integration/$bn"
            int_count=$((int_count + 1))
        fi
    fi
done
echo "  Processed $int_count integration tests"

# =========================================================================
# Step 8: Move system tests
# =========================================================================
echo "Step 8: Moving system tests..."

sys_count=0

# System compiler tests
for f in test/system/compiler/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/system/compiler/$bn" ]; then
            # Already in place
            :
        fi
        sys_count=$((sys_count + 1))
    fi
done

# Interpreter sample tests
for f in test/system/interpreter/sample/python_inspired_sample/*_spec.spl; do
    if [ -f "$f" ]; then
        sys_count=$((sys_count + 1))
    fi
done

# DAP tests
for f in test/system/dap/*_spec.spl; do
    if [ -f "$f" ]; then
        sys_count=$((sys_count + 1))
    fi
done

# Watcher tests
for f in test/system/watcher/*_spec.spl; do
    if [ -f "$f" ]; then
        sys_count=$((sys_count + 1))
    fi
done

# FFI tests
for f in test/system/ffi/*_spec.spl test/system/ffi/*_test.spl; do
    if [ -f "$f" ]; then
        sys_count=$((sys_count + 1))
    fi
done

# Move platform tests
for f in test/platform/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/system/platform/$bn" ]; then
            cp "$f" "test/system/platform/$bn"
            sys_count=$((sys_count + 1))
        fi
    fi
done

echo "  Processed $sys_count system tests"

# =========================================================================
# Step 9: Move remaining categorized tests
# =========================================================================
echo "Step 9: Moving remaining tests..."

remaining=0

# Diagnostics → test/unit/app/diagnostics/
for f in test/diagnostics/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/diagnostics/$bn" ]; then
            cp "$f" "test/unit/app/diagnostics/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Debug → test/unit/app/debug/
mkdir -p test/unit/app/debug
for f in test/debug/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/debug/$bn" ]; then
            cp "$f" "test/unit/app/debug/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Meta → test/unit/app/meta/
mkdir -p test/unit/app/meta
for f in test/meta/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/meta/$bn" ]; then
            cp "$f" "test/unit/app/meta/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Benchmarks → test/benchmark/
for f in test/benchmarks/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/benchmark/$bn" ]; then
            cp "$f" "test/benchmark/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Baremetal → test/system/baremetal/
mkdir -p test/system/baremetal
for f in test/baremetal/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/system/baremetal/$bn" ]; then
            cp "$f" "test/system/baremetal/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Specs → test/feature/ or test/unit/std/
for f in test/specs/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/feature/$bn" ]; then
            cp "$f" "test/feature/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Test framework → test/unit/app/test_runner/
for f in test/test_framework/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/app/test_runner/$bn" ]; then
            cp "$f" "test/unit/app/test_runner/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Runtime tests
for f in test/runtime/*_spec.spl test/runtime/*_test.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/std/$bn" ]; then
            cp "$f" "test/unit/std/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# Remote tests → test/integration/
for f in test/remote/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/integration/$bn" ]; then
            cp "$f" "test/integration/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

# tmp tests → delete or move to fixtures
for f in test/tmp/*_spec.spl test/tmp/*_test.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/unit/std/$bn" ]; then
            cp "$f" "test/unit/std/$bn"
            remaining=$((remaining + 1))
        fi
    fi
done

echo "  Moved $remaining remaining tests"

# =========================================================================
# Step 10: Move the deep test/lib/std/unit/* hierarchy
# =========================================================================
echo "Step 10: Moving deep lib/std/unit hierarchy..."

deep_count=0

# These are organized by topic - flatten into appropriate unit test dirs
# test/lib/std/unit/app/* → test/unit/app/
for f in $(find test/lib/std/unit/app -name '*_spec.spl' -o -name '*_test.spl' 2>/dev/null); do
    bn=$(basename "$f")
    # Determine destination based on path
    if echo "$f" | grep -q "/cli/"; then
        dest="test/unit/app/cli/$bn"
    elif echo "$f" | grep -q "/formatter/"; then
        dest="test/unit/app/formatter/$bn"
    elif echo "$f" | grep -q "/lsp/"; then
        mkdir -p test/unit/app/lsp
        dest="test/unit/app/lsp/$bn"
    elif echo "$f" | grep -q "/test_runner/"; then
        dest="test/unit/app/test_runner/$bn"
    elif echo "$f" | grep -q "/utils/"; then
        dest="test/unit/app/utils/$bn"
    else
        dest="test/unit/app/$bn"
    fi
    if [ ! -f "$dest" ]; then
        cp "$f" "$dest"
        deep_count=$((deep_count + 1))
    fi
done

# test/lib/std/unit/compiler/* → test/unit/compiler/
for f in $(find test/lib/std/unit/compiler -name '*_spec.spl' -o -name '*_test.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if echo "$f" | grep -q "/linker/"; then
        dest="test/unit/compiler/linker/$bn"
    elif echo "$f" | grep -q "/loader/"; then
        mkdir -p test/unit/compiler/loader
        dest="test/unit/compiler/loader/$bn"
    else
        dest="test/unit/compiler/$bn"
    fi
    if [ ! -f "$dest" ]; then
        cp "$f" "$dest"
        deep_count=$((deep_count + 1))
    fi
done

# test/lib/std/unit/mcp/* → test/unit/app/mcp/
for f in $(find test/lib/std/unit/mcp -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/app/mcp/$bn" ]; then
        cp "$f" "test/unit/app/mcp/$bn"
        deep_count=$((deep_count + 1))
    fi
done

# test/lib/std/unit/lsp/* → test/unit/app/lsp/
for f in $(find test/lib/std/unit/lsp -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    mkdir -p test/unit/app/lsp
    if [ ! -f "test/unit/app/lsp/$bn" ]; then
        cp "$f" "test/unit/app/lsp/$bn"
        deep_count=$((deep_count + 1))
    fi
done

# test/lib/std/unit/parser/* → test/unit/compiler/parser/
for f in $(find test/lib/std/unit/parser -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/compiler/parser/$bn" ]; then
        cp "$f" "test/unit/compiler/parser/$bn"
        deep_count=$((deep_count + 1))
    fi
done

# test/lib/std/unit/hir/* → test/unit/compiler/
mkdir -p test/unit/compiler/hir
for f in $(find test/lib/std/unit/hir -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/compiler/hir/$bn" ]; then
        cp "$f" "test/unit/compiler/hir/$bn"
        deep_count=$((deep_count + 1))
    fi
done

# test/lib/std/unit/codegen/* → test/unit/compiler/codegen/
for f in $(find test/lib/std/unit/codegen -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/compiler/codegen/$bn" ]; then
        cp "$f" "test/unit/compiler/codegen/$bn"
        deep_count=$((deep_count + 1))
    fi
done

# Remaining deep unit tests → appropriate dirs based on topic
for topic in collections concurrency config console contracts dap diagram exp failsafe ffi fs game_engine host improvements infra interpreter lms macros ml ml/engine ml/torch physics/collision physics/constraints physics/core physics/dynamics sdn shell spec syntax testing todo_tests tooling tooling/compiler ui ui/gui ui/tui units verification verification/lean; do
    src_dir="test/lib/std/unit/$topic"
    if [ -d "$src_dir" ]; then
        # Map topics to new locations
        case "$topic" in
            collections|concurrency|sdn|spec|testing|syntax|shell)
                dest_dir="test/unit/std"
                ;;
            config|console|ffi|fs|host)
                dest_dir="test/unit/std"
                ;;
            dap)
                mkdir -p test/unit/app/dap
                dest_dir="test/unit/app/dap"
                ;;
            diagram)
                mkdir -p test/unit/app/diagram
                dest_dir="test/unit/app/diagram"
                ;;
            exp)
                mkdir -p test/unit/std/exp
                dest_dir="test/unit/std/exp"
                ;;
            failsafe)
                mkdir -p test/unit/std/failsafe
                dest_dir="test/unit/std/failsafe"
                ;;
            game_engine)
                mkdir -p test/unit/lib/game_engine
                dest_dir="test/unit/lib/game_engine"
                ;;
            improvements)
                mkdir -p test/unit/std/improvements
                dest_dir="test/unit/std/improvements"
                ;;
            infra)
                mkdir -p test/unit/std/infra
                dest_dir="test/unit/std/infra"
                ;;
            interpreter)
                dest_dir="test/unit/app/interpreter"
                ;;
            lms)
                mkdir -p test/unit/lib/lms
                dest_dir="test/unit/lib/lms"
                ;;
            macros)
                mkdir -p test/unit/compiler/macros
                dest_dir="test/unit/compiler/macros"
                ;;
            ml|ml/engine|ml/torch)
                mkdir -p test/unit/lib/ml
                dest_dir="test/unit/lib/ml"
                ;;
            physics/*)
                mkdir -p test/unit/lib/physics
                dest_dir="test/unit/lib/physics"
                ;;
            tooling|tooling/*)
                mkdir -p test/unit/app/tooling
                dest_dir="test/unit/app/tooling"
                ;;
            todo_tests)
                mkdir -p test/unit/app/todo
                dest_dir="test/unit/app/todo"
                ;;
            ui|ui/gui|ui/tui)
                mkdir -p test/unit/app/ui
                dest_dir="test/unit/app/ui"
                ;;
            units)
                mkdir -p test/unit/std/units
                dest_dir="test/unit/std/units"
                ;;
            contracts)
                mkdir -p test/unit/std/contracts
                dest_dir="test/unit/std/contracts"
                ;;
            verification|verification/lean)
                mkdir -p test/unit/compiler/verification
                dest_dir="test/unit/compiler/verification"
                ;;
            *)
                dest_dir="test/unit/std"
                ;;
        esac

        for f in $(find "$src_dir" -maxdepth 1 -name '*_spec.spl' -o -name '*_test.spl' 2>/dev/null); do
            bn=$(basename "$f")
            if [ ! -f "$dest_dir/$bn" ]; then
                cp "$f" "$dest_dir/$bn"
                deep_count=$((deep_count + 1))
            fi
        done
    fi
done

echo "  Moved $deep_count deep hierarchy tests"

# =========================================================================
# Step 11: Move remaining lib tests
# =========================================================================
echo "Step 11: Moving remaining lib tests..."

librem_count=0

# test/lib/std/features/* → test/feature/
for f in $(find test/lib/std/features -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/feature/$bn" ]; then
        cp "$f" "test/feature/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# test/lib/std/spec/* → test/unit/std/
for f in $(find test/lib/std/spec -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/std/$bn" ]; then
        cp "$f" "test/unit/std/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# test/lib/std/parser/* → test/unit/compiler/parser/
for f in $(find test/lib/std/parser -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/compiler/parser/$bn" ]; then
        cp "$f" "test/unit/compiler/parser/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# test/lib/std/type_checker/* → test/unit/compiler/
mkdir -p test/unit/compiler/type_checker
for f in $(find test/lib/std/type_checker -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/compiler/type_checker/$bn" ]; then
        cp "$f" "test/unit/compiler/type_checker/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# test/lib/std/type_inference/* → test/unit/compiler/
mkdir -p test/unit/compiler/type_inference
for f in $(find test/lib/std/type_inference -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/compiler/type_inference/$bn" ]; then
        cp "$f" "test/unit/compiler/type_inference/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# test/lib/std/system/* → test/system/
for f in $(find test/lib/std/system -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/system/$bn" ]; then
        cp "$f" "test/system/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# test/lib/std/fixtures/* → test/fixtures/
for f in $(find test/lib/std/fixtures -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/unit/std/$bn" ]; then
        cp "$f" "test/unit/std/$bn"
        librem_count=$((librem_count + 1))
    fi
done

# Top-level test/lib/*_spec.spl
for f in test/lib/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        case "$bn" in
            database*) dest="test/unit/lib/database/$bn" ;;
            *) dest="test/unit/lib/$bn" ;;
        esac
        if [ ! -f "$dest" ]; then
            cp "$f" "$dest"
            librem_count=$((librem_count + 1))
        fi
    fi
done

# test/lib/hooks/*
for f in test/lib/hooks/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        mkdir -p test/unit/std/hooks
        if [ ! -f "test/unit/std/hooks/$bn" ]; then
            cp "$f" "test/unit/std/hooks/$bn"
            librem_count=$((librem_count + 1))
        fi
    fi
done

echo "  Moved $librem_count remaining lib tests"

# =========================================================================
# Step 12: Move intensive tests → test/integration/ (slow tests)
# =========================================================================
echo "Step 12: Moving intensive tests..."

intense_count=0
for f in $(find test/intensive -name '*_spec.spl' 2>/dev/null); do
    bn=$(basename "$f")
    if [ ! -f "test/integration/$bn" ]; then
        cp "$f" "test/integration/$bn"
        intense_count=$((intense_count + 1))
    fi
done
echo "  Moved $intense_count intensive tests"

# =========================================================================
# Step 13: Move system collection & interpreter tests
# =========================================================================
echo "Step 13: Moving remaining system tests..."

sysrem_count=0
for f in test/system/collections/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        if [ ! -f "test/feature/$bn" ]; then
            cp "$f" "test/feature/$bn"
            sysrem_count=$((sysrem_count + 1))
        fi
    fi
done

# System interpreter tests already in place
for f in test/system/interpreter/*_spec.spl; do
    if [ -f "$f" ]; then
        sysrem_count=$((sysrem_count + 1))
    fi
done

# System-level specs from test/system/ directly
for f in test/system/*_spec.spl; do
    if [ -f "$f" ]; then
        sysrem_count=$((sysrem_count + 1))
    fi
done

echo "  Processed $sysrem_count system tests"

# =========================================================================
# Step 14: Move src/ spec files to test/
# =========================================================================
echo "Step 14: Moving src/ spec files..."

src_count=0

# FFI gen specs
for f in src/app/ffi_gen.specs/*_spec.spl src/app/ffi_gen/specs/*_spec.spl; do
    if [ -f "$f" ]; then
        bn=$(basename "$f")
        mkdir -p test/unit/app/ffi_gen
        if [ ! -f "test/unit/app/ffi_gen/$bn" ]; then
            cp "$f" "test/unit/app/ffi_gen/$bn"
            src_count=$((src_count + 1))
        fi
    fi
done

# Lint spec
if [ -f "src/app/fix/rules/impl/lint_spec.spl" ]; then
    if [ ! -f "test/unit/app/fix/lint_spec.spl" ]; then
        cp src/app/fix/rules/impl/lint_spec.spl test/unit/app/fix/lint_spec.spl
        src_count=$((src_count + 1))
    fi
fi

echo "  Moved $src_count src/ spec files"

# =========================================================================
# Step 15: Set up symlinks for imports
# =========================================================================
echo "Step 15: Setting up symlinks..."

# Ensure test/lib/ symlinks exist for the new structure
# The symlinks should point from new test locations to src/
cd "$ROOT"

# Create symlinks in new unit dirs that may need imports
for new_dir in test/unit/std test/unit/lib test/unit/app test/unit/compiler test/feature test/integration test/system; do
    if [ -d "$new_dir" ] && [ ! -L "$new_dir/lib" ] && [ ! -d "$new_dir/lib" ]; then
        # Link to existing test/lib which has the symlinks to src/
        ln -sf "$ROOT/test/lib" "$new_dir/lib" 2>/dev/null || true
    fi
done

echo "  Symlinks configured."

# =========================================================================
# Summary
# =========================================================================
echo ""
echo "=== Migration Complete ==="
new_count=$(find test/unit test/feature test/integration test/system test/benchmark -name '*_spec.spl' -o -name '*_test.spl' 2>/dev/null | wc -l)
echo "Files in new structure: $new_count"
echo ""
echo "New structure:"
for d in test/unit test/unit/std test/unit/lib test/unit/app test/unit/compiler test/feature test/integration test/system test/benchmark; do
    if [ -d "$d" ]; then
        count=$(find "$d" -maxdepth 1 -name '*_spec.spl' -o -name '*_test.spl' 2>/dev/null | wc -l)
        sub_count=$(find "$d" -name '*_spec.spl' -o -name '*_test.spl' 2>/dev/null | wc -l)
        echo "  $d: $count direct, $sub_count total"
    fi
done
