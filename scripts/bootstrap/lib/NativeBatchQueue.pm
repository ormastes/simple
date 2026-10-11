package NativeBatchQueue;
use strict;
use warnings;
use Exporter 'import';
use Digest::SHA qw(sha256_hex);
our @EXPORT_OK=qw(queue_request queue_record baseline_copy);
sub baseline_copy {my($s)=@_;return {paths=>[@{$s->{accepted}}],result=>$s->{baseline_result},sha256=>$s->{baseline_result_sha256}};}
sub same_paths {join("\n",@{$_[0]}) eq join("\n",@{$_[1]});}

# Probes retain their original baseline. Merges always use the latest fully
# verified accepted set. A passing probe never implicitly proves that merge.
sub queue_request {
    my($s)=@_;$s->{blocked} and die "lane blocked; changed configuration required\n";
    @{$s->{queue}} or return;
    my $task=shift @{$s->{queue}};
    my $base=$task->{phase} eq 'merge'?baseline_copy($s):$task->{baseline};
    my @selected=(@{$base->{paths}},@{$task->{added}});
    return {phase=>$task->{phase},added=>$task->{added},selected=>\@selected,baseline=>$base,
        origin=>$task->{origin},independent_proof=>$task->{independent_proof},
        ordered_paths_sha256=>sha256_hex(join('',map {"$_\n"} @selected))};
}
sub queue_record {
    my($s,$request,$outcome)=@_;my $status=$outcome->{status};
    if($status eq 'BLOCKED') {$s->{blocked}={request=>$request,outcome=>$outcome};return 'BLOCKED';}
    if($status eq 'PASS') {
        my @wanted=(@{$s->{accepted}},@{$request->{added}});
        if(same_paths($request->{selected},\@wanted)) {
            $s->{accepted}=[@{$request->{selected}}];
            $s->{baseline_result}=$outcome->{verified_result};
            $s->{baseline_result_sha256}=$outcome->{verified_result_sha256};
            return 'ACCEPTED';
        }
        $request->{phase} eq 'probe' or die "merge baseline drifted while trial active\n";
        unshift @{$s->{queue}},{phase=>'merge',added=>$request->{added},origin=>$request->{origin},
            independent_proof=>$outcome->{verified_result}};
        return 'UNION_REQUIRED';
    }
    $status eq 'FAIL' or die "invalid queue outcome\n";
    my @added=@{$request->{added}};
    if(@added>1) {
        my @left=splice(@added,0,int(@added/2));
        my @children=map {+{phase=>$request->{phase},added=>$_,baseline=>$request->{baseline},
            origin=>$request->{id},independent_proof=>$request->{independent_proof}}} (\@left,\@added);
        unshift @{$s->{queue}},@children;
        push @{$s->{failed_combinations}},{request=>$request,outcome=>$outcome};
        return 'SPLIT';
    }
    if($request->{phase} eq 'merge') {
        push @{$s->{interactions}},{candidate=>$added[0],selected=>$request->{selected},
            accepted=>[@{$s->{accepted}}],baseline_result=>$request->{baseline}{result},
            independent_proof=>$request->{independent_proof},evidence=>$outcome->{evidence},
            reason=>'Candidate subset passed independently but its cumulative union failed; no single-file causality claimed.'};
        return 'INTERACTION';
    }
    return 'QUARANTINE';
}
1;
