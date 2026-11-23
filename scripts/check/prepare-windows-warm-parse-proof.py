import hashlib
import json
from pathlib import Path
import re

root = Path('source')
path = root / 'test/01_unit/app/cli/build_parallel_perf_mem_regression_spec.spl'
source = path.read_text(encoding='utf-8')
start = source.index('    it "hits disk frontend parse cache on warm second pass')
end = source.index('\n    it ', start + 1)
block = source[start:end]
header = '''use std.spec.{step}
use app.io.env_ops.{env_get, env_set, env_unset}
use app.io.file_ops.{path_absolute}
use app.io.time_ops.{time_now_unix_micros}
use std.io_runtime.{dir_create_all, dir_remove_all, file_write}
use app.cli.native_build_main.{native_build_bind_cache_dirs_from_args_v1}
use compiler.frontend.frontend.{parse_full_frontend, Logger}
use compiler.frontend.frontend_parse_cache.{frontend_parse_cache_hits, frontend_parse_cache_misses}
use compiler.frontend._FlatAstBridge.module_assembly.{flat_parse_module_body_calls}
'''
lines = []
calls = 0
for line in block.splitlines():
    if '= parse_full_frontend(' in line:
        calls += 1
        lines.append(f'        print "WARM-PARSE before {calls}"')
        lines.append(line)
        lines.append(f'        print "WARM-PARSE after {calls}"')
    else:
        lines.append(line)
assert calls == 6
out = root / 'warm-parse-proof'
out.mkdir(exist_ok=False)
(out / 'isolated_spec.spl').write_text(header + 'describe "isolated warm parse":\n' + '\n'.join(lines) + '\n', encoding='utf-8')
(out / 'inputs.json').write_text(json.dumps({
    'source': 'b63dce1068c2fc515a4e3ad05e137476909ed105',
    'original_spec_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    'exact_case_sha256': hashlib.sha256(block.encode()).hexdigest(),
    'instrumentation': 'before/after markers only around six unchanged parse calls',
    'producer_source': '042a7e14d251bee7309cfae1b3bd38aeb67745c8',
    'producer_differs_from_original_b63': True, 'admission': 'none'
}, indent=2), encoding='utf-8')
