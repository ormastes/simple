#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";
use NativeBatchQueue qw(queue_request queue_record baseline_copy);
use Test::More;
sub initial {
    my($paths)=@_;my $s={accepted=>['base'],baseline_result=>'base-proof',baseline_result_sha256=>'base-sha',queue=>[],interactions=>[],failed_combinations=>[]};
    push @{$s->{queue}},{phase=>'probe',added=>$paths,baseline=>baseline_copy($s)};return $s;
}
sub result {my($name,$status)=@_;return {status=>$status,verified_result=>"proof-$name",verified_result_sha256=>"sha-$name",evidence=>"diagnostic-$name"};}
sub take {my($s,$id)=@_;my $r=queue_request($s);$r->{id}=$id;return $r;}
sub record {my($s,$r,$status)=@_;return queue_record($s,$r,result($r->{id},$status));}
subtest 'root nested-failure counterexample schedules and proves survivor union' => sub {
    my $s=initial([qw(A B C D)]);
    my $all=take($s,'all');is(record($s,$all,'FAIL'),'SPLIT','whole remainder splits');
    my $ab=take($s,'ab');is(record($s,$ab,'FAIL'),'SPLIT','left subtree splits');
    my $a=take($s,'a');is(record($s,$a,'PASS'),'ACCEPTED','A accepted with baseline');
    my $b=take($s,'b');is_deeply($b->{selected},[qw(base B)],'B probe retains original baseline');
    is(record($s,$b,'FAIL'),'QUARANTINE','B is an independently rejected file');
    my $cd=take($s,'cd');is_deeply($cd->{selected},[qw(base C D)],'right subtree uses original baseline');
    is(record($s,$cd,'PASS'),'UNION_REQUIRED','right pass cannot implicitly prove accepted union');
    is_deeply($s->{accepted},[qw(base A)],'C,D not counted attached before merge');
    is(scalar @{$s->{interactions}},0,'does not invent both-halves-passed interaction');
    my $union=take($s,'acd');is_deeply($union->{selected},[qw(base A C D)],'requests exact missing survivor union');
    is($union->{baseline}{result},'proof-a','union carries current accepted native authority');
    is(record($s,$union,'PASS'),'ACCEPTED','verified union accepted');
    is_deeply($s->{accepted},[qw(base A C D)],'all proven survivors retained');
    ok(!queue_request($s),'finite queue converges');
};
subtest 'passing halves and failed union retain interaction and unrelated progress' => sub {
    my $s=initial([qw(A B C D)]);my %seen;my @executed;my @reused;
    while(my $r=queue_request($s)) {
        $r->{id}='trial-'.(@executed+@reused+1);my $key=join(',',@{$r->{selected}});
        my $o=$seen{$key};
        if($o){push @reused,$key;}else{push @executed,$key;my %in=map {$_=>1} @{$r->{selected}};$o=result($r->{id},$in{A}&&$in{B}?'FAIL':'PASS');$seen{$key}=$o;}
        queue_record($s,$r,$o);last if @executed+@reused>30;
    }
    is_deeply($s->{accepted},[qw(base A C D)],'unrelated C,D accepted after A+B interaction');
    is(scalar @{$s->{interactions}},1,'one interaction recorded without whole-file causality');
    is($s->{interactions}[0]{candidate},'B','excluded candidate identified without sole-cause claim');
    ok(grep($_ eq 'base,A,B',@reused),'unchanged failing combination reuses prior evidence');
    is(scalar(grep($_ eq 'base,A,B',@executed)),1,'failed combination natively evaluated only once');
    ok(grep($_ eq 'base,A,C,D',@executed),'missing survivor union actually evaluated');
};
subtest 'failed union subdivides candidates instead of discarding them all' => sub {
    my $s=initial([qw(C D)]);$s->{accepted}=[qw(base A)];$s->{baseline_result}='proof-a';
    my $cd=take($s,'cd');is(record($s,$cd,'PASS'),'UNION_REQUIRED','independent CD pass');
    my $acd=take($s,'acd');is(record($s,$acd,'FAIL'),'SPLIT','union failure splits new candidate subset');
    my $ac=take($s,'ac');is(record($s,$ac,'FAIL'),'INTERACTION','C conflicts with accepted A');
    my $ad=take($s,'ad');is_deeply($ad->{selected},[qw(base A D)],'D still attempted with accepted survivors');
    is(record($s,$ad,'PASS'),'ACCEPTED','D retained after actual cumulative pass');
    is_deeply($s->{accepted},[qw(base A D)],'does not discard entire independently passing half');
};
subtest 'all independent bad-file combinations retain every good survivor' => sub {
    for my $mask(0..15) {
        my @files=qw(A B C D);my %bad=map {$files[$_]=>1} grep {$mask & (1<<$_)} 0..3;
        my $s=initial([@files]);my @excluded;my $steps=0;
        while(my $r=queue_request($s)) {
            $r->{id}='oracle-'.++$steps;last if $steps>40;
            my $status=grep($bad{$_},@{$r->{selected}})?'FAIL':'PASS';
            my $action=record($s,$r,$status);push @excluded,@{$r->{added}} if $action eq 'QUARANTINE';
        }
        is_deeply($s->{accepted},['base',grep {!$bad{$_}} @files],"mask $mask keeps all and only verified good files");
        is_deeply([sort @excluded],[sort keys %bad],"mask $mask isolates each bad source");
        ok($steps<=40,"mask $mask bounded termination");
    }
};
subtest 'infrastructure stops without source quarantine' => sub {
    my $s=initial([qw(A B)]);my $r=take($s,'oom');is(record($s,$r,'BLOCKED'),'BLOCKED','infrastructure classified separately');
    is_deeply($s->{accepted},['base'],'accepted proof unchanged');
    my $ok=eval {queue_request($s);1};ok(!$ok,'same blocked configuration never retries automatically');
    is(scalar @{$s->{interactions}},0,'resource failure not called interaction');
};
done_testing();
