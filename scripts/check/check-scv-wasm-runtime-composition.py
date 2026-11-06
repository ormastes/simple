#!/usr/bin/env python3
"""Source composition regression; runtime behavior is tested by the real C fixture."""
from pathlib import Path

root = Path(__file__).resolve().parents[2]
bridge = 'runtime_scv_wasm_ffi'
build = (root / 'src/compiler_rust/runtime/build.rs').read_text()
compile_body = build.split('fn compile_c_runtime_sources()', 1)[1].split('fn ', 1)[0]
exports = build.split('const LINKED_C_SOURCES:', 1)[1].split('];', 1)[0]
assert compile_body.count(f'"{bridge}.c"') == 1, 'compiled provider must occur once'
assert exports.count(f'"{bridge}.c"') == 1, 'compiled provider must be scanned for exports'
for suffix in ('c', 'h'):
    assert f'cargo:rerun-if-changed=../../runtime/{bridge}.{suffix}' in build
seed = (root / 'src/compiler_rust/compiler/src/pipeline/native_project/tools.rs').read_text()
assert seed.count(f'"{bridge}.c"') == 1, 'portable core-C provider must occur once'
assert seed.count(f'"{bridge}.h"') == 1, 'portable fingerprint must include bridge header'
pure = (root / 'src/compiler/70.backend/backend/runtime_compiler.spl').read_text()
core = pure.split('pub fn runtime_core_c_sources_v1()', 1)[1].split('pub fn ', 1)[0]
assert core.count(f'"{bridge}"') == 1, 'pure-Simple core-C provider must occur once'
assert pure.count(f'"{bridge}"') == 2, 'core-C and ordinary compositions need the bridge'
print('PASS: SCV bridge runtime source compositions')
