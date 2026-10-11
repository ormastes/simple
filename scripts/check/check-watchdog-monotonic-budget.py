#!/usr/bin/env python3
from pathlib import Path
import re,subprocess,tempfile,sys
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'resource/process-tree-rss-watchdog.pl'
s=p.read_text()
helper=re.search(r'^sub monotonic_time \{[^\n]+\}',s,re.M).group()
timeout=re.search(r"if \((\$opt\{'timeout-seconds'\} && monotonic_time\(\) - \$started >= \$opt\{'timeout-seconds'\})\)",s).group(1)
grace=re.search(r'while \((monotonic_time\(\) < \$grace_end)\)',s).group(1)
duration=re.search(r'my \$duration_ms = (\(monotonic_time\(\) - \$sample_started_at\) \* 1000);',s).group(1)
remaining=re.search(r'my \$remaining = (\$opt\{\x27interval-ms\x27\} / 1000 - \(monotonic_time\(\) - \$sample_started\));',s).group(1)
script='''use strict;use warnings;use Test::More tests => 8;
our ($mono,$wall)=(100,1000);
sub CLOCK_MONOTONIC(){ 7 }
sub clock_gettime { die "wrong clock" unless $_[0]==CLOCK_MONOTONIC; return $mono; }
sub time { return $wall; }
'''+helper+'''
my %opt=('timeout-seconds'=>10,'interval-ms'=>100);
my $started=100;
$mono=109;$wall=1000000;
ok(!('''+timeout+'''), 'forward civil jump cannot prematurely expire monotonic timeout');
$mono=111;$wall=-1000000;
ok(('''+timeout+'''), 'backward civil jump cannot extend timeout');
my $sample_started_at=200;$mono=200.05;$wall=9000000;
ok(abs(('''+duration+''')-50)<0.001,'sample duration uses monotonic delta after forward jump');
$wall=-9000000;
ok(abs(('''+duration+''')-50)<0.001,'sample duration survives backward jump');
my $sample_started=200;
ok(abs(('''+remaining+''')-0.05)<0.001,'sampling cadence remaining budget is monotonic');
my $grace_end=305;$mono=304;$wall=9999999;
ok(('''+grace+'''),'forward civil jump does not cut grace period');
$mono=306;$wall=-9999999;
ok(!('''+grace+'''),'backward civil jump does not extend grace period');
$mono=123.25;is(monotonic_time(),123.25,'actual diagnostic helper requests CLOCK_MONOTONIC');
'''
# The workload/watchdog main is never imported or executed. Only its exact
# accessor and elapsed expressions run with controlled wall and monotonic clocks.
with tempfile.TemporaryDirectory(prefix='simple-watchdog-clock-contract-') as directory:
    q=Path(directory)/'contracts.pl'
    q.write_text(script)
    result=subprocess.run(['perl',str(q)],timeout=15)
raise SystemExit(result.returncode)
