#!/usr/bin/env python3
"""Extract real declaration closure and get_type for a scoped native regression.

This does not qualify imports or a bootstrap phase. No payload records are
mocked: each declaration is copied from its production owner and hashed.
"""
import argparse
import collections
import hashlib
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--value-source', type=Path)
args = parser.parse_args()
repo = args.repo.resolve()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
(out / 'src').mkdir()
index = collections.defaultdict(list)
rows = subprocess.check_output(['git', 'grep', '-n', '-E',
    r'^(pub )?(struct|enum|class|type) [A-Za-z_][A-Za-z_0-9]*',
    'HEAD', '--', 'src/compiler', 'src/lib/common'], cwd=repo, text=True)
for row in rows.splitlines():
    _, path, line, text = row.split(':', 3)
    name = re.match(r'(?:pub )?(?:struct|enum|class|type) (\w+)', text)[1]
    index[name].append(path)
value_path = 'src/compiler/00.common/runtime_value_v1.spl'
mir_path = 'src/compiler/50.mir/mir_types.spl'
for name in ['Value', 'EnumPayloadValue', 'FunctionValue', 'ClosureValue', 'ObjectValue', 'ValueCaptureMap']:
    index[name] = [value_path]
index['Span'] = ['src/lib/common/diagnostics/span.spl']
for name in ['Result', 'Option', 'Dict', 'Array', 'Some', 'None', 'Ok', 'Err']:
    index.pop(name, None)
priority = ['mir_types', 'mir_instruction_graph', 'mir_instruction_support',
    'mir_instruction_kinds', 'hir_types', 'hir_definitions', 'parser_types',
    'diagnostics/span', 'attributes.spl']
cache = {}
def read(path):
    if path not in cache:
        cache[path] = (repo / path).read_text()
    return cache[path]
def extract(text, pattern, indent):
    lines = text.splitlines(True)
    start = next(i for i, line in enumerate(lines) if re.match(pattern, line))
    end = start + 1
    while end < len(lines) and (not lines[end].strip() or lines[end].startswith(indent)):
        end += 1
    return ''.join(lines[start:end])
def method(text, name):
    return extract(text, r'    (?:static fn|fn) ' + name + r'\(', '        ')
queue = ['Value', 'MirType', 'MirTypeKind']
seen = {}
while queue:
    name = queue.pop()
    if name in seen:
        continue
    options = index[name]
    path = next((p for hint in priority for p in options if hint in p), options[0])
    text = extract(read(path), r'(?:pub )?(?:struct|enum|class|type) ' + name + r'\b', ' ')
    seen[name] = (path, text)
    cleaned = re.sub(r'"""[\s\S]*?"""', '', text)
    cleaned = '\n'.join(line.split('#')[0] for line in cleaned.splitlines())
    queue.extend(token for token in re.findall(r'\b[A-Z][A-Za-z_0-9]*\b', cleaned)
                 if token in index and token not in seen)
value_text = args.value_source.read_text() if args.value_source else read(value_path)
parts = [text for path, text in seen.values()]
parts += ['impl Value:\n' + method(value_text, 'get_type')]
parts += ['impl MirType:\n' + ''.join(method(read(mir_path), name) for name in ['i64', 'f64', 'bool', 'unit'])]
harness = (repo / 'test/01_unit/compiler/runtime_value_get_type_native.spl').read_text()
parts += [re.sub(r'^use .*\n', '', harness, flags=re.M)]
(out / 'src/main.spl').write_text('\n'.join(parts))
provenance = 'declarations |name, owner, sha256|\n'
for name, (path, text) in sorted(seen.items()):
    provenance += f'    {name}, {path}, {hashlib.sha256(text.encode()).hexdigest()}\n'
provenance += '\nget_type_sha256: "' + hashlib.sha256(method(value_text, 'get_type').encode()).hexdigest() + '"\n'
(out / 'provenance.sdn').write_text(provenance)
print(f'Extracted {len(seen)} production declarations into {out}')
