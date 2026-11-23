"""Verify and extract one exact target DLL; never interpret drive paths as hosts."""
import argparse
import hashlib
import json
import pathlib
import struct
import tarfile

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--archive', type=pathlib.Path, required=True)
p.add_argument('root', type=pathlib.Path)
a = p.parse_args()
expected_archive = 'bb7bb7654b33d5aa8712acb837c963b2e0c56352560c76105270a3268c665c21'
expected_helper = '298e3ec7e6816f51813ea32a180b0a698ae806f4cc8cae286f7b41aff773fe84'
member_name = 'llvm-mingw-20260922-ucrt-ubuntu-22.04-x86_64/x86_64-w64-mingw32/bin/libunwind.dll'
checksum = hashlib.sha256()
with a.archive.open('rb') as stream:
    for chunk in iter(lambda: stream.read(1024*1024), b''):
        checksum.update(chunk)
assert checksum.hexdigest() == expected_archive, 'toolchain archive digest mismatch'
with tarfile.open(a.archive, 'r:xz') as archive:
    member = archive.getmember(member_name)
    assert member.isfile() and 0 < member.size < 10*1024*1024, 'unexpected DLL member type/size'
    dll = archive.extractfile(member).read()

def imports(data):
    pe = struct.unpack_from('<I', data, 0x3c)[0]
    assert data[pe:pe+4] == b'PE\0\0'
    machine, count = struct.unpack_from('<HH', data, pe+4)
    assert machine == 0x8664, 'expected x86_64 PE'
    optional = pe+24
    optional_size = struct.unpack_from('<H', data, pe+20)[0]
    assert struct.unpack_from('<H', data, optional)[0] == 0x20b
    sections = [struct.unpack_from('<IIII', data, optional+optional_size+40*i+8) for i in range(count)]
    def offset(rva):
        for virtual_size, base, size, file_offset in sections:
            if base <= rva < base+max(virtual_size, size):
                result = file_offset+rva-base
                assert result < len(data)
                return result
        raise AssertionError(('unmapped import RVA', rva))
    at = offset(struct.unpack_from('<I', data, optional+112+8)[0])
    names = []
    while True:
        descriptor = struct.unpack_from('<IIIII', data, at)
        if not any(descriptor):
            break
        start = offset(descriptor[3])
        end = data.index(b'\0', start)
        names.append(data[start:end].decode('ascii').lower())
        at += 20
    assert names, 'missing import inventory'
    return names

system = {'kernel32.dll', 'ntdll.dll', 'gdi32.dll', 'user32.dll',
          'bcryptprimitives.dll', 'ws2_32.dll', 'oleaut32.dll', 'ole32.dll',
          'mswsock.dll', 'bcrypt.dll', 'advapi32.dll', 'd3d11.dll',
          'shell32.dll', 'crypt32.dll', 'psapi.dll'}
helper = (a.root/'process-provider.exe').read_bytes()
assert hashlib.sha256(helper).hexdigest() == expected_helper, 'helper changed'
helper_imports, dll_imports = imports(helper), imports(dll)
non_system = lambda names: sorted(set(n for n in names if n not in system and not n.startswith('api-ms-win-')))
assert non_system(helper_imports) == ['libunwind.dll'], ('unowned helper DLL', helper_imports)
assert not non_system(dll_imports), ('unowned transitive DLL', dll_imports)
sha = hashlib.sha256(dll).hexdigest()
assert sha == '5de310284e361c8d10a92e0a18f8b17d2d5a0de1d091d9e3c0b92d86f9f6c7c2', 'target DLL digest mismatch'
(a.root/'libunwind.dll').write_bytes(dll)
(a.root/'dll.sha').write_text(sha+'  '+str(a.root/'libunwind.dll').replace('\\', '/')+'\n')
record = {'archive_sha256': expected_archive, 'member': member_name, 'dll_sha256': sha,
          'machine': 'AMD64', 'helper_sha256': expected_helper,
          'helper_imports': helper_imports, 'dll_imports': dll_imports}
(a.root/'dll-intake.json').write_text(json.dumps(record, indent=2), encoding='utf-8')
print(json.dumps({'machine': 'AMD64', 'dll_sha256': sha, 'non_system_dependencies': ['libunwind.dll'], 'transitive_non_system_dependencies': []}))
