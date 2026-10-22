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
my $tmp=tempdir(CLEANUP=>1);my $tool="$FindBin::Bin/../native-batch-bisect.pl";
sub put {make_path(dirname($_[0]));open my $f,'>',$_[0] or die $!;print {$f} $_[1];}
sub get {open my $f,'<',$_[0] or die $!;local $/;return <$f>;}
sub save {put($_[0],JSON::PP->new->canonical->encode($_[1]));}
sub obj {decode_json(get($_[0]));}
sub run {
    my @args=@_;my $pid=fork();defined($pid) or die $!;
    if(!$pid){open STDOUT,'>',"$tmp/tool.log" or die $!;open STDERR,'>&',\*STDOUT;exec $^X,$tool,@args;die $!;}
    waitpid($pid,0);return $?==0;
}
# Synthetic receipts below exercise coordinator validation, not native coverage.
my @paths=map {"test/01_unit/compiler/interpreter/${_}_spec.spl"} qw(base A B C D);
my $body="describe \"fixture\":\n    it \"original assertion\":\n        expect(1).to_equal(1)\n";
put("$tmp/source/$_",$body) for @paths;
put("$tmp/canonical.tsv","subsystem\tlevel\tpath\tsha256\n".join('',map {"interpreter\t01_unit\t$_\t".sha256_hex($body)."\n"} @paths));
put("$tmp/ordered.txt",join('',map {"$_\n"} @paths));
put("$tmp/compiler", "\x7fELFcompiler-fixture");
put("$tmp/positive.native", "\x7fELFpositive-fixture");put("$tmp/negative.native", "\x7fELFnegative-fixture");
put("$tmp/review.txt", "Test fixture migration review, not native product qualification.\n");
my $compiler_sha=sha256_hex(get("$tmp/compiler"));
my $runtime_sha="a"x64;
sub initial_build {
    my($backend)=@_;
    put("$tmp/build.env", "schema=simple-restricted-native-adapter-build-v1\nformal_product_pass=0\nbackend=$backend\ncompiler_sha256=$compiler_sha\nsource_root=$tmp/source\nruntime_capsule_sha256=$runtime_sha\n");
}
save("$tmp/green.json",{schema=>'simple-restricted-native-adapter-result-v1',status=>'RESTRICTED_NATIVE_GATE_PASS',
    formal_product_pass=>JSON::PP::false,variants=>{positive=>{run_exit=>0,source_sha256=>sha256_hex($body),binary_sha256=>sha256_hex(get("$tmp/positive.native"))},negative=>{run_exit=>1,binary_sha256=>sha256_hex(get("$tmp/negative.native"))}}});
for my $backend(qw(llvm cranelift)) {
    save("$tmp/authority-$backend.json",{schema=>'simple-reviewed-native-authority-v1',backend=>$backend,
        result_sha256=>sha256_hex(get("$tmp/green.json")),reviewed_by=>'controller-test-fixture',review_evidence=>"$tmp/review.txt",review_evidence_sha256=>sha256_hex(get("$tmp/review.txt")),
        compiler_path=>"$tmp/compiler",compiler_sha256=>$compiler_sha,runtime_capsule_sha256=>$runtime_sha,variants=>{map {$_=>{binary_path=>"$tmp/$_.native",binary_sha256=>sha256_hex(get("$tmp/$_.native"))}} qw(positive negative)}});
}
put("$tmp/diagnostic.log","compiler rejected fixture B\n");
sub trial {
    my($n,$status,$expected)=@_;
    ok(run('next',"$tmp/lane"),"emit trial $n");
    my $id=sprintf('trial-%04d',$n);my $r=obj("$tmp/lane/$id/request.json");
    is_deeply($r->{selected},[map {$paths[$_]} @$expected],"trial $n exact source selection");
    my $out={status=>$status,reason=>'fixture diagnostic',repair_owner=>'fixture owner',failure_class=>'compile',evidence=>"$tmp/diagnostic.log"};
    if($status eq 'PASS') {
        my $proof="$tmp/proof-$n";
        save("$proof/manifest.json",{ordered_paths_sha256=>$r->{ordered_paths_sha256},canonical_inventory_sha256=>sha256_hex(get("$tmp/canonical.tsv")),source_root=>"$tmp/source"});
        put("$proof/positive.native","\x7fELFpositive-$n");put("$proof/negative.native","\x7fELFnegative-$n");
        put("$proof/build.env", "schema=simple-restricted-prefix-build-v1\nformal_product_pass=0\nbackend=cranelift\ncompiler_sha256=$compiler_sha\nworkspace=$tmp/source\nruntime_cwd=$tmp/source\nruntime_capsule_sha256=$runtime_sha\nmanifest_sha256=".sha256_hex(get("$proof/manifest.json"))."\n");
        save("$proof/result.json",{schema=>'simple-restricted-prefix-result-v1',status=>'RESTRICTED_PREFIX_GATE_PASS',formal_product_pass=>JSON::PP::false,
            build_sha256=>sha256_hex(get("$proof/build.env")),backend=>'cranelift',compiler_sha256=>$compiler_sha,workspace=>"$tmp/source",runtime_capsule_sha256=>$runtime_sha,
            detached_owners=>0,quarantined_assertions=>0,compiled_owners=>scalar(@$expected),executed_owners=>scalar(@$expected),manifest_sha256=>sha256_hex(get("$proof/manifest.json")),variants=>{map {$_=>{binary_sha256=>sha256_hex(get("$proof/$_.native"))}} qw(positive negative)}});
        $out->{verified_result}="$proof/result.json";
    }
    save("$tmp/outcome.json",$out);
    if($n==6) {
        my $build=get("$tmp/proof-$n/build.env");(my $wrong=$build)=~s/backend=cranelift/backend=llvm/;put("$tmp/proof-$n/build.env",$wrong);
        ok(!run('record',"$tmp/lane","$tmp/outcome.json"),'LLVM native receipt cannot satisfy Cranelift lane');
        is_deeply(obj("$tmp/lane/state.json")->{accepted},[@paths[0,1]],'wrong backend does not inflate accepted union');
        (my $producer=$build)=~s/compiler_sha256=$compiler_sha/compiler_sha256=@{['0'x64]}/;put("$tmp/proof-$n/build.env",$producer);
        ok(!run('record',"$tmp/lane","$tmp/outcome.json"),'different native producer rejected');
        put("$tmp/proof-$n/build.env",$build);
        my $receipt=obj("$tmp/proof-$n/result.json");
        # Authentic-shaped LLVM result/build hashes cannot be relabelled by
        # changing only adjacent build.env to the requested Cranelift lane.
        my %llvm=%$receipt;$llvm{backend}='llvm';$llvm{build_sha256}=sha256_hex($wrong);
        save("$tmp/proof-$n/result.json",\%llvm);
        ok(!run('record',"$tmp/lane","$tmp/outcome.json"),'LLVM receipt plus relabelled Cranelift build rejected');
        for my $key(qw(backend compiler_sha256 workspace runtime_capsule_sha256 build_sha256)) {
            my %mismatch=%$receipt;$mismatch{$key}=$key eq 'backend' ? 'llvm' : $key eq 'workspace' ? "$tmp/other-source" : '0'x64;
            save("$tmp/proof-$n/result.json",\%mismatch);
            ok(!run('record',"$tmp/lane","$tmp/outcome.json"),"result $key mismatch rejected");
        }
        for my $key(qw(schema build_sha256 runtime_capsule_sha256)) {
            my %missing=%$receipt;delete $missing{$key};save("$tmp/proof-$n/result.json",\%missing);
            ok(!run('record',"$tmp/lane","$tmp/outcome.json"),"missing result $key rejected");
        }
        save("$tmp/proof-$n/result.json",$receipt);
        for my $key(qw(schema runtime_capsule_sha256)) {
            (my $missing=$build)=~s/^\Q$key\E=.*\n//m;put("$tmp/proof-$n/build.env",$missing);
            ok(!run('record',"$tmp/lane","$tmp/outcome.json"),"missing build $key rejected");
        }
        (my $other_runtime=$build)=~s/runtime_capsule_sha256=$runtime_sha/runtime_capsule_sha256=@{['b'x64]}/;
        put("$tmp/proof-$n/build.env",$other_runtime);
        my %other=%$receipt;$other{runtime_capsule_sha256}='b'x64;$other{build_sha256}=sha256_hex($other_runtime);
        save("$tmp/proof-$n/result.json",\%other);
        ok(!run('record',"$tmp/lane","$tmp/outcome.json"),'self-consistent other runtime rejected by reviewed lane');
        save("$tmp/proof-$n/result.json",$receipt);put("$tmp/proof-$n/build.env",$build);
        is_deeply(obj("$tmp/lane/state.json")->{accepted},[@paths[0,1]],'identity refusals never inflate accepted union');
        my $native=get("$tmp/proof-$n/positive.native");put("$tmp/proof-$n/positive.native","\x7fELFswapped-artifact");
        ok(!run('record',"$tmp/lane","$tmp/outcome.json"),'swapped result binary rejected');
        put("$tmp/proof-$n/positive.native",$native);
    }
    ok(run('record',"$tmp/lane","$tmp/outcome.json"),"record trial $n");
    return $r;
}
initial_build('cranelift');
ok(run('init',"$tmp/source","$tmp/canonical.tsv","$tmp/ordered.txt",'interpreter',4,"$tmp/lane","$tmp/green.json",'cranelift',"$tmp/authority-cranelift.json"),'initialize whole remaining batch');
trial(1,'FAIL',[0,1,2,3,4]);trial(2,'FAIL',[0,1,2]);trial(3,'PASS',[0,1]);trial(4,'FAIL',[0,2]);
my $cd=trial(5,'PASS',[0,3,4]);
is($cd->{baseline_result},"$tmp/green.json",'right subtree binds original proof, not accepted A proof');
is_deeply(obj("$tmp/lane/state.json")->{accepted},[@paths[0,1]],'right probe alone does not inflate native acceptance');
my $union=trial(6,'PASS',[0,1,3,4]);
is($union->{baseline_result},"$tmp/proof-3/result.json",'new union binds latest accepted A proof');
my $s=obj("$tmp/lane/state.json");
is_deeply($s->{accepted},[@paths[0,1,3,4]],'CLI preserves entire verified survivor union');
is(scalar @{$s->{interactions}},0,'nested failure does not fabricate interaction');
is(scalar @{$s->{quarantine}},1,'only B is excluded');
is($s->{quarantine}[0]{backend},'cranelift','backend outcome remains separate');
is(get($s->{quarantine}[0]{original_source}),$body,'original assertion bytes retained');
like(get($s->{quarantine}[0]{retained_fail_marker}),qr/assert\(false\)/,'excluded file has explicit nonpassing marker');
ok(run('next',"$tmp/lane"),'completion returns no new native trial');
like(get("$tmp/tool.log"),qr/NO_PENDING_BATCHES/,'completion is not a formal native PASS');
# Same canonical source selection can be prepared independently for LLVM.
initial_build('llvm');
ok(run('init',"$tmp/source","$tmp/canonical.tsv","$tmp/ordered.txt",'interpreter',4,"$tmp/llvm","$tmp/green.json",'llvm',"$tmp/authority-llvm.json"),'same source inventory starts independent LLVM lane');
ok(run('next',"$tmp/llvm"),'LLVM request generated');
is(get("$tmp/llvm/trial-0001/ordered-paths.txt"),get("$tmp/lane/trial-0001/ordered-paths.txt"),'both backends receive identical source list');
is(obj("$tmp/llvm/state.json")->{backend},'llvm','LLVM result authority separate');
ok(!run('init',"$tmp/source","$tmp/canonical.tsv","$tmp/ordered.txt",'interpreter',4,"$tmp/wrong-initial","$tmp/green.json",'cranelift',"$tmp/authority-llvm.json"),'wrong-backend initial migration mapping rejected');
# A reused failure must retain its exact original diagnostic bytes.
my $reuse=obj("$tmp/llvm/state.json");delete $reuse->{active};
$reuse->{queue}=[{phase=>'merge',added=>[@paths[1..4]]}];
my $initial=obj("$tmp/llvm/trial-0001/request.json");
put("$tmp/reused-diagnostic.log","original failure\n");
save("$tmp/reused-outcome.json",{status=>'FAIL',failure_class=>'compile',evidence=>"$tmp/reused-diagnostic.log",evidence_sha256=>sha256_hex(get("$tmp/reused-diagnostic.log"))});
$reuse->{decisions}{$initial->{ordered_paths_sha256}}={outcome=>"$tmp/reused-outcome.json",sha256=>sha256_hex(get("$tmp/reused-outcome.json"))};
$reuse->{trials}=[{id=>'trial-0001'}];save("$tmp/llvm/state.json",$reuse);
put("$tmp/reused-diagnostic.log","changed failure\n");
ok(!run('next',"$tmp/llvm"),'changed diagnostic prevents failure reuse');
like(get("$tmp/tool.log"),qr/prior diagnostic changed/,'failure reuse rejection identifies missing authority');
done_testing();
