#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use NativeAdapterEvidence qw(build_evidence previous_build_evidence);
use File::Temp qw(tempdir);
use Digest::SHA qw(sha256_hex);
use JSON::PP;
use Test::More;

# Receipt-contract tests only: fixtures cannot qualify native compilation.
my $root=tempdir(CLEANUP=>1);
my $json=JSON::PP->new->canonical;
my $sha='a' x 64;
my $runtime_sha='c' x 64;
sub check_previous { previous_build_evidence(@_, $runtime_sha) }
my $manifest="{\"source_root\":\"/lane\"}\n";
sub put { open my $f,'>:raw',"$root/$_[0]" or die $!; print {$f} $_[1]; close $f or die $!; }
put('manifest.json',$manifest);
my $body="schema=simple-restricted-prefix-build-v1\nformal_product_pass=0\nworkspace=/lane\nruntime_cwd=/lane\ncompiler_sha256=$sha\nbackend=llvm\nruntime_capsule_sha256=$runtime_sha\nmanifest_sha256=".sha256_hex($manifest)."\n";
sub setup {
    put('build.env',$body);
    my $b=build_evidence($root,0);
    put('result.json',$json->encode({schema=>'simple-restricted-prefix-result-v1',%$b}));
    return $b;
}
my $binding=setup();
is($binding->{build_sha256},sha256_hex($body),'result binds exact build bytes');
is_deeply(check_previous("$root/result.json",'/lane',$sha,'llvm'),$binding,'same producer/backend/workspace accepted');
eval {previous_build_evidence("$root/result.json",'/lane',$sha,'llvm','d' x 64)};
like($@,qr/previous build runtime_capsule_sha256 differs/,'reject another frozen runtime capsule');
for my $case (
    ['workspace','/other',$sha,'llvm'],
    ['compiler_sha256','/lane','b' x 64,'llvm'],
    ['backend','/lane',$sha,'cranelift']) {
    my ($field,@args)=@$case;
    eval {check_previous("$root/result.json",@args)};
    like($@,qr/previous build \Q$field\E differs/,"reject other $field before native execution");
}
for my $case (
    ['duplicate field',$body."backend=llvm\nruntime_capsule_sha256=$runtime_sha\n",qr/duplicate build field/],
    ['malformed field',$body."garbage\n",qr/malformed build field/],
    ['formal authority',do {(my $v=$body)=~s/formal_product_pass=0/formal_product_pass=1/;$v},qr/incorrect build authority/],
    ['invalid producer',do {(my $v=$body)=~s/$sha/bad/;$v},qr/invalid build producer/],
    ['unknown backend',do {(my $v=$body)=~s/backend=llvm/backend=unknown/;$v},qr/invalid build backend/],
    ['missing runtime capsule',do {(my $v=$body)=~s/runtime_capsule_sha256=[^\n]+\n//;$v},qr/invalid build runtime capsule/],
    ['runtime cwd',do {(my $v=$body)=~s/runtime_cwd=\/lane/runtime_cwd=\/other/;$v},qr/build runtime workspace differs/]) {
    setup();put('build.env',$case->[1]);eval {build_evidence($root,0)};
    like($@,$case->[2],"reject $case->[0]");
}
setup();put('manifest.json',$manifest." ");eval {build_evidence($root,0)};
like($@,qr/build manifest differs/,'reject changed compiled manifest');
put('manifest.json',$manifest);
setup();put('build.env',$body."threads=20\n");eval {check_previous("$root/result.json",'/lane',$sha,'llvm')};
like($@,qr/previous result build_sha256 differs/,'reject modified build bytes');
for my $key (qw(build_sha256 workspace compiler_sha256 backend runtime_capsule_sha256)) {
    my $b=setup();delete $b->{$key};
    put('result.json',$json->encode({schema=>'simple-restricted-prefix-result-v1',%$b}));
    eval {check_previous("$root/result.json",'/lane',$sha,'llvm')};
    like($@,qr/previous result \Q$key\E differs/,"reject missing result $key");
}
setup();unlink "$root/build.env" or die $!;eval {check_previous("$root/result.json",'/lane',$sha,'llvm')};
like($@,qr/missing\/linked build evidence/,'reject absent original build receipt');
my $legacy="schema=simple-restricted-native-adapter-build-v1\nformal_product_pass=0\nsource_root=/lane\ncompiler_sha256=$sha\nbackend=llvm\nruntime_capsule_sha256=$runtime_sha\n";
put('build.env',$legacy);put('result.json',$json->encode({schema=>'simple-restricted-native-adapter-result-v1'}));
is(check_previous("$root/result.json",'/lane',$sha,'llvm')->{build_sha256},sha256_hex($legacy),'legacy migration retains original matching build digest');
eval {check_previous("$root/result.json",'/lane',$sha,'cranelift')};
like($@,qr/previous build backend differs/,'legacy LLVM receipt cannot seed Cranelift lane');
eval {previous_build_evidence("$root/result.json",'/lane',$sha,'llvm','d' x 64)};
like($@,qr/previous build runtime_capsule_sha256 differs/,'legacy migration rejects another frozen runtime');
done_testing();
