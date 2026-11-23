"""Restore verified cache candidates only; queue verdicts remain historical evidence."""
import hashlib
import json
from pathlib import Path
import shutil

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
PARENT = 'ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'
MANIFEST = '072388108755a4b8534e5636f94eeaccd0506f36a297f15adb006b713ee72b66'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify_prior(old, manifest, expected_parent_line):
    terminal = json.loads((old/'evidence/terminal.json').read_text())
    assert terminal['source'] == SOURCE and terminal['parent_sha256'] == PARENT
    assert terminal['status'] == 'FAILED' and terminal['stage'] == 'canonical-phase2'
    assert terminal['parent_unchanged'] is True
    owner = dict(row.split('=', 1) for row in (old/'evidence/phase2.owner.env').read_text().splitlines() if '=' in row)
    assert owner['status'] == 'rss-cap-exceeded' and owner['exit_status'] == '88'
    assert owner['quiescent'] == '1' and owner['rss_cap_enforced'] == '1'
    assert owner['rss_limit_kib'] == str(terminal['cap_kib'])
    assert expected_parent_line in (old/'evidence/phase2.stdout').read_text().splitlines()
    assert digest(manifest) == MANIFEST
    rows = json.loads(manifest.read_text())
    cache = old/'cache'
    assert {p.relative_to(cache).as_posix() for p in cache.rglob('*') if p.is_file()} == {row['path'] for row in rows}
    return rows, cache

def install_candidates(rows, cache, dest):
    assert not dest.exists(), 'new attempt must start with no cache or queue'
    copied = []
    excluded = []
    for row in rows:
        rel = Path(row['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        original = cache/rel
        assert not original.is_symlink()
        assert original.stat().st_size == row['bytes'] and digest(original) == row['sha256']
        # Both HIR and MIR claim/terminal/pick ledgers are generation-specific.
        # Keep them in intake evidence, never install them into the new owner.
        if any(part.startswith(('queue-', 'mir-queue-')) for part in rel.parts):
            excluded.append(row['path'])
            continue
        target = dest/rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, target)
        assert digest(target) == row['sha256']
        copied.append(row['path'])
    return copied, excluded

def restore_cache(source, evidence):
    old = Path('intake/prior/source/build/ladder')
    manifest = Path(__file__).with_name('prior-cache-manifest.json')
    expected = 'Building phase 2 with ' + str(source/'build/ladder/in/linux-x86_64-p1/simple') + ' (phase 1)'
    rows, cache = verify_prior(old, manifest, expected)
    copied, excluded = install_candidates(rows, cache, source/'build/ladder/cache')
    result = {'prior_run':45262236182, 'prior_artifact':14864330203,
              'manifest_sha256':MANIFEST, 'copied_candidates':copied,
              'excluded_historical_queue_files':excluded,
              'reuse_status':'unqualified candidates; canonical cache checks must decide',
              'fresh_queue_required':True, 'scope_reduction':False}
    (evidence/'cache-intake.json').write_text(json.dumps(result, indent=2))
    return {'manifest_sha256':MANIFEST, 'copied_count':len(copied),
            'excluded_queue_count':len(excluded), 'reuse_status':result['reuse_status']}
