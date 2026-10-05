#!/usr/bin/env bash
# Linux ELF ownership regression; retain all objects, links and native results.
set -euo pipefail
cd "$(dirname "$0")/../../.."
out=${1:?usage: check_enum_mixed_owner.sh ABSOLUTE_OUTPUT_DIRECTORY}
case "$out" in /*) ;; *) echo 'output directory must be absolute' >&2; exit 2;; esac
mkdir -p "$out"
cc=${CC:-clang}
nm=${NM:-llvm-nm}
flags=(-std=c11 -O2 -g -ffunction-sections -fdata-sections -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -Isrc/runtime)
for unit in runtime runtime_native runtime_memory runtime_memtrack; do
    feature=()
    case "$unit" in runtime_memory|runtime_memtrack) feature=(-D_GNU_SOURCE);; esac
    timeout 60 "$cc" "${flags[@]}" "${feature[@]}" -c "src/runtime/$unit.c" -o "$out/$unit.o" >"$out/$unit.compile.log" 2>&1
done
timeout 30 "$cc" "${flags[@]}" -D_GNU_SOURCE -c src/runtime/test/enum_mixed_owner_selfcheck.c -o "$out/test.o"
timeout 30 "$cc" "${flags[@]}" -D_GNU_SOURCE -DENUM_LEGACY_ONLY -c src/runtime/test/enum_mixed_owner_selfcheck.c -o "$out/test-legacy.o"
for order in legacy-first native-first legacy-only; do
    objects=("$out/runtime.o" "$out/runtime_native.o")
    test_object="$out/test.o"
    case "$order" in
        native-first) objects=("$out/runtime_native.o" "$out/runtime.o");;
        legacy-only) objects=("$out/runtime.o"); test_object="$out/test-legacy.o";;
    esac
    # Ordinary runtime uses this flag for pre-existing duplicate C exports.
    timeout 30 "$cc" -Wl,--gc-sections -Wl,--allow-multiple-definition "$test_object" "${objects[@]}" "$out/runtime_memory.o" "$out/runtime_memtrack.o" -lm -lpthread -ldl -o "$out/$order" >"$out/$order.link.log" 2>&1
    timeout 10 "$out/$order" >"$out/$order.run.log" 2>&1
    cat "$out/$order.run.log"
done
"$nm" --print-file-name --defined-only "$out/runtime.o" "$out/runtime_native.o" | grep 'rt_enum_' >"$out/enum-symbols.txt"
sha256sum src/runtime/runtime.c src/runtime/runtime_native.c src/runtime/runtime_memory.c src/runtime/runtime_memtrack.c src/runtime/test/enum_mixed_owner_selfcheck.c >"$out/sources.sha256"
sha256sum "$out"/*.o "$out/legacy-first" "$out/native-first" "$out/legacy-only" >"$out/artifacts.sha256"
