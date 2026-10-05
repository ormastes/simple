use strict;
use warnings;
use FindBin;
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use Test::More;
sub read_file { open my $f,'<:raw',$_[0] or die $!; local $/; return <$f>; }
sub put { open my $f,'>:raw',$_[0] or die $!; print {$f} $_[1] or die $!; close $f or die $!; }
my $text=read_file("$FindBin::Bin/build-compiler-subsystem-test-product.shs");
$text =~ /(run_native_build\(\) \{.*?\n\})\n\nrun_native_tool/s or die 'native command owner unavailable';
my $owner=$1;
my $base=$^O =~ /msys|cygwin/ ? '/c/.simple-product-tests' : '/tmp';
make_path($base);
my $root=tempdir('timeout-XXXXXXXX',DIR=>$base,CLEANUP=>0);
note("retained command fixture: $root");
put("$root/producer", "#!/bin/sh\nprintf 'native_timeout=%s\\n' \"\$SIMPLE_NATIVE_FILE_TIMEOUT\"\nprintf 'arg=%s\\n' \"\$@\"\nexit 17\n");
put("$root/watchdog", "#!/bin/sh\nshift 2\nexec \"\$@\"\n");
chmod 0755,"$root/producer","$root/watchdog";
for my $timeout (0,19) {
    my $job="$root/job-$timeout"; make_path("$job/logs");
    my $script="#!/bin/sh\nset -u\ncompiler='$root/producer'\ncompiler_sha256=fixture\nsource_root='$root'\noverlay='$root'\njob_root='$job'\nruntime_authority='$root'\nthreads=80\nrss_cap_kib=5242880\nrss_mode=monitor\nbuild_timeout_seconds=$timeout\nwatchdog='$root/watchdog'\nproduct_frontend_environment='SIMPLE_SHARD_MEM_CLAMP=1'\n";
    put("$job/run.shs", $script . $owner . "\nrun_native_build generator src/app/example.spl '$job/product' cranelift\n");
    system('sh',"$job/run.shs");
    is($? >> 8,17,"native child raw status preserved (timeout $timeout)");
    my $log=read_file("$job/logs/generator.log");
    like($log,qr/^native_timeout=$timeout$/m,"actual child receives supported native timeout environment ($timeout)");
    unlike($log,qr/^arg=--timeout(?:=|$)/m,"no unsupported zero CLI timeout is sent ($timeout)");
    like(read_file("$job/logs/generator.command.tsv"),qr/^simple_native_file_timeout=$timeout$/m,"actual command evidence binds file timeout ($timeout)");
}
done_testing();
