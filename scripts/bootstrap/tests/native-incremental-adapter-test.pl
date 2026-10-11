#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use File::Basename qw(dirname);
use Digest::SHA qw(sha256_hex);
use JSON::PP;
use Test::More;
my $repo="$FindBin::Bin/../../..";
my $tmp=tempdir(CLEANUP=>1);
sub read_bytes {open my $f,'<:raw',$_[0] or die $!;local $/;return <$f>;}
sub write_bytes {make_path(dirname($_[0]));open my $f,'>:raw',$_[0] or die $!;print {$f} $_[1];close $f or die $!;}
my @paths=map {"test/01_unit/compiler/interpreter/${_}_spec.spl"} qw(while_body_scope logical_short_circuit mixed_numeric_arithmetic unsupported_fixture);
my $inventory="subsystem\tlevel\tpath\tsha256\n";
for my $i(0..$#paths) {
    my $body=$i==3?"describe \"unsupported\":\n    it \"retains original\":\n        expect([1]).to_equal([1])\n":read_bytes("$repo/$paths[$i]");
    write_bytes("$tmp/source/$paths[$i]",$body);
    $inventory.="interpreter\t01_unit\t$paths[$i]\t".sha256_hex($body)."\n";
}
write_bytes("$tmp/canonical.tsv",$inventory);
sub run_prefix {
    my($name,$paths,$previous,$subsystem)=@_;
    write_bytes("$tmp/$name.list",join('',map {"$_\n"} @$paths));
    my $pid=fork();defined($pid) or die $!;
    if(!$pid){open STDOUT,'>',"$tmp/$name.log" or die $!;open STDERR,'>&',\*STDOUT or die $!;
        exec $^X,"$repo/scripts/bootstrap/native-incremental-adapter.pl","$tmp/source","$tmp/canonical.tsv","$tmp/$name.list",
            ($subsystem//'interpreter'),"$tmp/$name",($previous eq '-'?'-':"$tmp/$previous/manifest.json");die $!;}
    waitpid($pid,0);return $?==0;
}
ok(run_prefix('one',[$paths[0]],'-'),'initial one-file generation');
ok(run_prefix('two',[@paths[0,1]],'one'),'append exactly one file');
my $p=decode_json(read_bytes("$tmp/two/manifest.json"));
is_deeply([@$p{qw(selected_owners attached_owners detached_owners compiled_owners executed_owners)}],[2,2,0,0,0],'generation does not claim native execution');
is(scalar(@{$p->{variants}{positive}{cases}}),4,'all four cases attached');
my $entry=read_bytes("$tmp/two/positive-entry.spl");
is(scalar(()=$entry=~/val adapter_actual_1: bool = false and \(1 \/ 0 == 0\)/g),1,'short-circuit expression preserved and evaluated once');
like($entry,qr/while i < 2:\n        val shadow = i \+ 5\n        i = i \+ 1/,'original while body preserved');
my $negative=read_bytes("$tmp/two/negative-sources/$paths[1]");
my $original=read_bytes("$tmp/source/$paths[1]");
(my $expected=$original)=~s/expect\(false and \(1 \/ 0 == 0\)\)\.to_equal\(false\)/expect(false and (1 \/ 0 == 0)).to_equal(true)/;
is($negative,$expected,'negative control mutates only newly added expected value');
is(read_bytes("$tmp/two/negative-sources/$paths[0]"),read_bytes("$tmp/source/$paths[0]"),'negative retains preceding source unchanged');
ok(run_prefix('jump',[@paths[0,1,2]],'one'),'append a batch of two owners');
my $batch=decode_json(read_bytes("$tmp/jump/manifest.json"));
is_deeply($batch->{added_paths},[@paths[1,2]],'batch records every added owner');
is(scalar(@{$batch->{variants}{positive}{cases}}),8,'batch includes all eight actual cases');
ok(!run_prefix('reorder',[@paths[1,0]],'one'),'reject reordered prefix');
ok(!run_prefix('duplicate',[@paths[0,0]],'one'),'reject duplicate owner');
ok(!run_prefix('foreign',[$paths[0]],'-','compiler'),'reject foreign subsystem');
ok(run_prefix('detached',[@paths[0,1,3]],'two'),'retain unsupported new owner without adapting it');
my $d=decode_json(read_bytes("$tmp/detached/manifest.json"));
is_deeply([@$d{qw(selected_owners attached_owners detached_owners compiled_owners executed_owners)}],[3,2,1,0,0],'detached source does not inflate coverage');
ok(!$d->{negative_control_available} && !-e "$tmp/detached/negative-entry.spl",'unsupported addition cannot pass native gate');
is(read_bytes("$tmp/detached/sources/$paths[3]"),read_bytes("$tmp/source/$paths[3]"),'unsupported original assertion retained verbatim');
ok(run_prefix('three',[@paths[0,1,2]],'two'),'next reviewed f64 file generates all cases');
ok(!run_prefix('two',[@paths[0,1]],'one'),'reject overwriting prior evidence');
write_bytes("$tmp/source/$paths[1]",$original."\n");
ok(!run_prefix('changed',[@paths[0,1]],'one'),'reject changed canonical source');
done_testing();
