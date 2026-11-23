"""Fail closed on undeclared non-system DLLs in the retained process proof."""
import hashlib
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
system = {'kernel32.dll', 'ntdll.dll', 'gdi32.dll', 'user32.dll',
          'bcryptprimitives.dll', 'ws2_32.dll', 'oleaut32.dll', 'ole32.dll',
          'mswsock.dll', 'bcrypt.dll', 'advapi32.dll', 'd3d11.dll',
          'shell32.dll', 'crypt32.dll', 'psapi.dll'}
records = {}
for log in ['process-provider-imports.stdout', 'dll-imports.txt']:
    names = re.findall(r'^\s+Name: ([^\r\n]+)', (root/log).read_text(encoding='utf-8'), re.M)
    assert names, ('missing import inventory', log)
    for name in names:
        lower = name.lower()
        assert lower in system or lower.startswith('api-ms-win-') or lower == 'libunwind.dll', ('unowned DLL', name)
    records[log] = names
dll = root/'libunwind.dll'
assert dll.is_file()
records['libunwind_sha256'] = hashlib.sha256(dll.read_bytes()).hexdigest()
records['archive_sha256'] = 'bb7bb7654b33d5aa8712acb837c963b2e0c56352560c76105270a3268c665c21'
(root/'dll-intake.json').write_text(json.dumps(records, indent=2), encoding='utf-8')
