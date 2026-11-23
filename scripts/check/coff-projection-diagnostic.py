import hashlib, json, pathlib, subprocess
out = pathlib.Path('projection-evidence')
out.mkdir()
results = []
tool = '/usr/bin/x86_64-w64-mingw32-objcopy'
(out/'version.txt').write_bytes(subprocess.check_output([tool, '--version']))
for name, symbol in [('closure.o', 'dependency'), ('retained-closure.o', 'rt_file_exists')]:
    source = pathlib.Path('retained')/name
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    for operation in ['localize', 'weaken', 'strip-section', 'copy']:
        flags = {'localize': ['--localize-symbol='+symbol], 'weaken': ['--weaken-symbol='+symbol], 'strip-section': ['--remove-section=.ctors'], 'copy': []}[operation]
        dest = out/(name+'.'+operation+'.o')
        argv = [tool, *flags, str(source), str(dest)]
        result = subprocess.run(argv, capture_output=True, timeout=10)
        (out/(name+'.'+operation+'.stderr')).write_bytes(result.stderr)
        results.append(dict(source=name, sha256=digest, operation=operation, argv=argv, exit=result.returncode, stderr=result.stderr.decode(errors='replace')))
        if result.returncode == 0:
            (out/(name+'.'+operation+'.symbols')).write_bytes(subprocess.check_output(['/usr/bin/x86_64-w64-mingw32-nm', str(dest)]))
    assert hashlib.sha256(source.read_bytes()).hexdigest() == digest
(out/'results.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
print(json.dumps(results))
