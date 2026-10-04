#!/usr/bin/env python3
"""Actual git-archive regression for tracked paths omitted by cache attributes."""
from pathlib import Path
import io
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[3]
# Exact tracked paths missing during FreeBSD product snapshot projection.
PATHS = """examples/10_tooling/llm_cli_tools/test/system/llm/llm_math_system_spec.spl
examples/10_tooling/obsidian-search/test/system/obsidian_search_spec.spl
src/app/build/bootstrap_receipt_main.spl
src/app/build/bootstrap_receipt_planner.spl
src/app/build/cli_entry.spl
src/app/build/feature_flags.spl
src/app/build/opt_remarks.spl
src/app/build/sffi_lint.spl
src/app/build/targets/action_identity.spl
src/app/build/targets/artifact_receipt.spl
src/app/build/targets/bootstrap_policy.spl
src/app/build/targets/build_explain.spl
src/app/build/targets/build_targets.spl
src/app/build/targets/change_classifier.spl
src/app/build/targets/target_executor.spl
src/app/build/targets/target_resolve.spl
src/app/build/targets/targets_cli.spl
src/lib/gc_async_mut/engine/build/__init__.spl
src/lib/gc_async_mut/engine/build/build_config.spl
src/lib/gc_async_mut/engine/build/build_pipeline.spl
src/lib/nogc_async_mut/engine/build/__init__.spl
src/lib/nogc_async_mut/engine/build/build_config.spl
src/lib/nogc_async_mut/engine/build/build_pipeline.spl
src/lib/nogc_sync_mut/engine/build/__init__.spl
src/lib/nogc_sync_mut/engine/build/build_config.spl
src/lib/nogc_sync_mut/engine/build/build_pipeline.spl
""".splitlines()
with tempfile.TemporaryDirectory(prefix='simple-archive-root.') as tmp:
    repo = Path(tmp)
    def git(*args):
        return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.PIPE)
    git('init', '-q')
    payload = {}
    for name in PATHS:
        payload[name] = (ROOT / name).read_bytes()
        dest = repo / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(payload[name])
    for name in ('build/cache.o', 'system/cache.bin'):
        dest = repo / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(b'root cache must stay excluded\n')
    attributes = (ROOT / '.gitattributes').read_text()
    def archive(attr):
        (repo / '.gitattributes').write_text(attr)
        git('add', '.')
        git('-c', 'user.name=ArchiveFixture', '-c', 'user.email=fixture@example.invalid',
            'commit', '-qm', 'archive attribute fixture')
        with tarfile.open(fileobj=io.BytesIO(git('archive', '--format=tar', 'HEAD'))) as tar:
            return {item.name: tar.extractfile(item).read() for item in tar if item.isfile()}
    old = archive(attributes.replace('/build export-ignore', 'build export-ignore')
                           .replace('/system export-ignore', 'system export-ignore'))
    assert all(name not in old for name in PATHS), 'fixture must reproduce all 26 omissions'
    fixed = archive(attributes)
    assert len(PATHS) == 26
    for name, content in payload.items():
        assert fixed.get(name) == content, f'tracked source missing or changed: {name}'
    for name in ('build/cache.o', 'system/cache.bin'):
        assert name not in fixed, f'root cache exported: {name}'
print('PASS: git archive retains all 26 tracked nested build/system sources; root build/system caches remain excluded')
