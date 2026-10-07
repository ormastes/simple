"""Exercise actual extracted helpers without materializing links or touching checkout.

Windows host regression/benchmark: --before ORIGINAL --candidate CANDIDATE
--tree immutable-git-ls-tree.raw --output PRIVATE_EMPTY_DIRECTORY.
No compiler/bootstrap invocation. All cases continue independently on failure.
"""
import argparse
import json
import pathlib
import subprocess
import time


def main():
    ap = argparse.ArgumentParser()
    for name in ('before', 'candidate', 'tree', 'output'):
        ap.add_argument('--' + name, required=True, type=pathlib.Path)
    ap.add_argument('--only-memory', action='store_true')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    old = args.before.read_text(encoding='utf-8')
    new = args.candidate.read_text(encoding='utf-8')
    rows = []

    def check(name, fn):
        if args.only_memory and name != 'paired-native-memory-regression':
            return
        start = time.perf_counter()
        try:
            detail = fn()
            rows.append(dict(name=name, status='PASS', seconds=time.perf_counter()-start, detail=detail))
        except Exception as exc:
            rows.append(dict(name=name, status='FAIL', seconds=time.perf_counter()-start, error=str(exc)))

    def write(name, data):
        path = args.output / name
        path.write_bytes(data.encode('utf-8') if isinstance(data, str) else data)
        return path

    def bash(script):
        r = subprocess.run(['C:/Program Files/Git/bin/bash.exe', str(script)], capture_output=True, timeout=180)
        if r.returncode:
            raise AssertionError(r.stderr.decode('utf-8', errors='replace')[-2000:])
        return r.stdout

    def posix(path):
        s = str(path.resolve()).replace('\\', '/')
        return '/' + s[0].lower() + s[2:]

    def quote(text):
        return "'" + text.replace("'", "'\\''") + "'"

    # Execute the exact production helper, not a Python behavioral model.
    start = new.index('    public static void IndexTrackedTree(')
    end = new.index('    static void DrainGitError(', start)
    method = new[start:end]
    cs = ('using System; using System.IO; using System.Text; using System.Collections.Generic;\n'
          'public static class MaterializerPerfTest { public static readonly HashSet<string> Tracked = '
          'new HashSet<string>(StringComparer.Ordinal);\n' + method + '}')
    write('helper.cs', cs)
    oid = 'a' * 40
    fixture = ('100644 '+oid+' ordinary name\0' + '040000 '+oid+' src\0' +
               ''.join('120000 '+oid+' '+p+'\0' for p in [
                   'a link', '한글/é', 'target/skip', 'x/target/skip', 'x/targetish/keep',
                   'target', 'embedded\nnewline', 'tab\tname', 'back\\slash', '-dash', 'quote"name']))
    write('fixture.raw', fixture)
    write('malformed.raw', 'bad\0')
    # Old code also treats a final non-NUL row differently in its second Bash
    # pass; git ls-tree always supplies NUL. Assert this input contract below.
    ps = r'''$ErrorActionPreference='Stop'
Add-Type -Path (Join-Path $PSScriptRoot 'helper.cs')
$results=@()
foreach($name in @('fixture','representative','malformed','bad-output')) {
  try {
    $file=if($name -eq 'representative') { '__TREE__' } elseif($name -eq 'malformed') { Join-Path $PSScriptRoot 'malformed.raw' } else { Join-Path $PSScriptRoot 'fixture.raw' }
    $text=[Text.UTF8Encoding]::new($false,$true).GetString([IO.File]::ReadAllBytes($file))
    [MaterializerPerfTest]::Tracked.Clear()
    [GC]::Collect(); $before=[GC]::GetTotalMemory($true)
    $sw=[Diagnostics.Stopwatch]::StartNew()
    $out=if($name -eq 'bad-output') { Join-Path $PSScriptRoot 'absent/list' } else { Join-Path $PSScriptRoot ($name+'.list') }
    $threw=$false
    try { [MaterializerPerfTest]::IndexTrackedTree($text,$out) } catch { $threw=$true; if($name -notin @('malformed','bad-output')) { throw } }
    $sw.Stop()
    if(($name -in @('malformed','bad-output')) -and !$threw) { throw 'expected failure' }
    $results+=@{name=$name;status='PASS';seconds=$sw.Elapsed.TotalSeconds;tracked=[MaterializerPerfTest]::Tracked.Count;retained_bytes=([GC]::GetTotalMemory($true)-$before);peak_rss=[Diagnostics.Process]::GetCurrentProcess().PeakWorkingSet64}
  } catch { $results+=@{name=$name;status='FAIL';error=$_.Exception.ToString()} }
}
$results | ConvertTo-Json -Depth 4 | Set-Content -Encoding UTF8 (Join-Path $PSScriptRoot 'native-helper-results.json')
if(@($results | Where-Object status -eq 'FAIL').Count) { exit 1 }
'''.replace('__TREE__', str(args.tree.resolve()).replace("'", "''"))
    write('test-helper.ps1', ps)

    def helper():
        r = subprocess.run(['powershell.exe', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', str(args.output/'test-helper.ps1')], capture_output=True, timeout=60)
        result = json.loads((args.output/'native-helper-results.json').read_text(encoding='utf-8-sig'))
        assert r.returncode == 0, result
        return result
    check('actual-CSharp-tree-helper-and-resource-observation', helper)

    def tree_compare():
        a = old.index("while IFS= read -r -d '' entry; do")
        b = old.index("while IFS= read -r -d '' path", a)
        body = old[a:b]
        exclusion = old[old.index('materializer_is_excluded_path() {'):old.index('\n}\n', old.index('materializer_is_excluded_path() {'))+3]
        details = []
        for name, raw in [('fixture', args.output/'fixture.raw'), ('representative', args.tree)]:
            data = raw.read_bytes()
            assert data.endswith(b'\0')
            out = args.output/(name+'.old.list')
            script = write(name+'.sh', 'set -eu\n'+exclusion+'\nraw_links_list='+quote(posix(raw))+'\nlinks_list='+quote(posix(out))+'\n: >"$links_list"\n'+body)
            started = time.perf_counter(); bash(script); elapsed = time.perf_counter()-started
            expected = out.read_bytes(); actual = (args.output/(name+'.list')).read_bytes()
            assert expected == actual, name+' byte mismatch'
            details.append(dict(name=name, old_seconds=elapsed, input_bytes=len(data), list_bytes=len(actual), links=actual.count(b'\0')//2))
        return details
    check('old-new-tree-byte-equivalence-and-host-benchmark', tree_compare)

    def path_compare():
        cases = ['/c/dev/repo/normal/file.spl', '/D/space here/한글/é.spl', '/c/COM0/COM10', '/c/conx/targetish',
                 '/c/CoN', '/c/nUl.txt', '/c/aUx/x', '/c/LpT9.log', '/c/cOm¹.txt', '/c/LPT²',
                 '/c//double', '/c/../escape', '/c/./dot', '/c/trailing.', '/c/trailing ', '/c/a:b',
                 '/c/a?b', '/c/a*b', '/c/a|b', '/c/a<b', '/c/a>b', '/c/a"b', '/c/a\\b', '/c/new\nline',
                 '/c/tab\tname', '/c/end/', '/ab/path', 'C:/native', '/c']
        outputs = []
        durations = []
        for label, script in [('before', old), ('after', new)]:
            i = script.index('receipt_to_win_path() {'); j = script.index('\n}\n', i)+3
            calls = ''.join('if result=$(receipt_to_win_path '+quote(case)+'); then printf "OK:%s\\n" "$result"; else printf "REJECT\\n"; fi\n' for case in cases)
            source = write('paths-'+label+'.sh', 'set -u\n'+script[i:j]+'\n'+calls)
            started=time.perf_counter(); outputs.append(bash(source)); durations.append(time.perf_counter()-started)
        assert outputs[0] == outputs[1], 'path output/rejection mismatch'
        result=outputs[1].decode('utf-8').splitlines()
        assert all(x.startswith('OK:') for x in result[:4]), result
        assert all(x == 'REJECT' for x in result[4:]), result
        return dict(cases=len(cases), before_seconds=durations[0], after_seconds=durations[1], before_external_tr_calls='one per component plus drive', after_external_tr_calls=0)
    check('path-rejections-byte-equivalence-and-host-benchmark', path_compare)

    def guards():
        for token in ['pending_policy_allows "$path" "$target_rel"', 'native_action publish',
                      'receipt.policy-digest-mismatch', 'Git HEAD changed before receipt publish',
                      'native_action prepare', 'target pending: $path']:
            assert token in new, token
        assert 'foreach (string row in tree.Split' in new
        assert new.count('foreach (string row in tree.Split') == 1
        assert "while IFS= read -r -d '' entry" not in new
        assert 'MATERIALIZER_LINKS="$(to_win_path "$links_list")"' in new
        assert new.index('start_native_batch || materializer_fail') < new.index("while IFS= read -r -d '' path")
        return 'Native held-handle, publication, pending policy and bootstrap error gates retained; no per-entry native subprocess added.'
    check('security-and-resource-structure-regressions', guards)

    def paired_memory():
        i = old.index("        foreach (string row in tree.Split('\\0')) {")
        j = old.index('        PolicyBytes =', i)
        baseline = 'public static void IndexTrackedTree(string tree,string linksPath) {\n'+old[i:j]+'}\n'
        values = []
        for label, body in [('before', baseline), ('after', method)]:
            code = ('using System;using System.IO;using System.Text;using System.Collections.Generic; '
                    'public static class PairedResource {static readonly HashSet<string> Tracked='
                    'new HashSet<string>(StringComparer.Ordinal);'+body+'}')
            code_file = write(label+'-resource.cs', code)
            ps = r'''$ErrorActionPreference='Stop'
Add-Type -Path '__CS__'
$text=[Text.UTF8Encoding]::new($false,$true).GetString([IO.File]::ReadAllBytes('__TREE__'))
[GC]::Collect(); $before=[GC]::GetTotalMemory($true)
$sw=[Diagnostics.Stopwatch]::StartNew()
[PairedResource]::IndexTrackedTree($text,'__OUT__'); $sw.Stop()
@{seconds=$sw.Elapsed.TotalSeconds;retained_bytes=([GC]::GetTotalMemory($true)-$before);peak_rss=[Diagnostics.Process]::GetCurrentProcess().PeakWorkingSet64} | ConvertTo-Json -Compress
'''.replace('__CS__', str(code_file).replace("'", "''")).replace('__TREE__', str(args.tree).replace("'", "''")).replace('__OUT__', str(args.output/'memory.list').replace("'", "''"))
            script = write(label+'-resource.ps1', ps)
            r = subprocess.run(['powershell.exe', '-NoProfile', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-File', str(script)], capture_output=True, timeout=30, check=True)
            values.append(dict(label=label, **json.loads(r.stdout)))
        # Generous host-noise allowance, still rejecting an extra retained tree
        # or unbounded helper allocations on this representative fixture.
        assert values[1]['retained_bytes'] <= values[0]['retained_bytes']+8*1024*1024, values
        assert values[1]['peak_rss'] <= values[0]['peak_rss']+32*1024*1024, values
        return values
    check('paired-native-memory-regression', paired_memory)
    write('result.json', json.dumps(dict(cases=rows, passed=sum(r['status']=='PASS' for r in rows), failed=sum(r['status']=='FAIL' for r in rows), native_bootstrap_run=False), indent=2))
    print(json.dumps(dict(passed=sum(r['status']=='PASS' for r in rows), failed=sum(r['status']=='FAIL' for r in rows), result=str(args.output/'result.json'))))
    return int(any(r['status']=='FAIL' for r in rows))


if __name__ == '__main__':
    raise SystemExit(main())
