#!/usr/bin/env python3
"""Exercise repository export attributes through actual Git archives."""
import argparse
import io
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile


def check(attributes, git):
    roots = ('build', 'tmp', 'artifacts', 'node-compile-cache', 'system')
    kept = {f'src/app/{name}/source.spl': f'fn {name.replace("-", "_")}_source():\n    7\n'.encode()
            for name in roots}
    kept['src/lib/nogc_sync_mut/system/source.spl'] = b'fn system_source():\n    9\n'
    excluded = {f'{name}/cache.txt': b'local cache\n' for name in roots}
    excluded['src/compiler_rust/target/cache.txt'] = b'compiled cache\n'
    excluded['src/app/vscode_extension/node_modules/cache.txt'] = b'npm cache\n'
    with tempfile.TemporaryDirectory(prefix='simple-archive-source-') as temporary:
        folder = Path(temporary)
        def run(*args):
            return subprocess.check_output([git, '-C', str(folder), *args], stderr=subprocess.PIPE)
        run('init', '--quiet')
        (folder / '.gitattributes').write_bytes(attributes)
        for relative, data in {**kept, **excluded}.items():
            target = folder / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        run('-c', 'core.autocrlf=false', 'add', '--all')
        run('-c', 'user.name=Archive regression', '-c', 'user.email=archive@example.invalid',
            '-c', 'commit.gpgsign=false', 'commit', '--quiet', '-m', 'archive fixture')
        with tarfile.open(fileobj=io.BytesIO(run('archive', '--format=tar', 'HEAD'))) as archive:
            names = set(archive.getnames())
            failures = []
            for relative, data in kept.items():
                if relative not in names:
                    failures.append(f'missing source: {relative}')
                elif archive.extractfile(relative).read() != data:
                    failures.append(f'changed source: {relative}')
            for relative in excluded:
                if relative in names:
                    failures.append(f'exported cache: {relative}')
            if failures:
                raise RuntimeError('; '.join(failures))
    print(f'PASS: {len(kept)} nested sources retained byte-for-byte; {len(excluded)} cache files excluded')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attributes', type=Path, default=Path(__file__).resolve().parents[2] / '.gitattributes')
    parser.add_argument('--git', default=shutil.which('git'))
    arguments = parser.parse_args()
    if not arguments.git:
        parser.error('Git is required')
    check(arguments.attributes.read_bytes(), arguments.git)
