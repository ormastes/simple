#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductSelection qw(product_selection);
use NativeBatchQueue qw(queue_request queue_record baseline_copy);
use NativeAdapterEvidence qw(previous_build_evidence);
use JSON::PP;
use Digest::SHA qw(sha256_hex);
use File::Path qw(make_path);
use File::Basename qw(dirname);

# Evidence coordinator only. Native compilation/assertion semantics stay in
# the selected product runner. Each command is bounded; no polling/retry loop.
sub bytes { open my $f,'<:raw',$_[0] or die "$! $_[0]\n"; local $/; return <$f>; }
sub write_bytes { make_path(dirname($_[0])); open my $f,'>:raw',$_[0] or die $!; print {$f} $_[1]; close $f or die $!; }
my $json=JSON::PP->new->canonical->pretty;
sub save { write_bytes($_[0],$json->encode($_[1])); }
sub read_json { return decode_json(bytes($_[0])); }
sub require_absolute { for(@_) { m{\A/} && !/[\r\n\0]/ or die "absolute paths required\n"; } }
sub fields {
    my($path)=@_;my %f;
    for(split /\n/,bytes($path)) { /\A([^=]+)=(.*)\z/ or die "invalid build field\n";exists($f{$1}) and die "duplicate build field\n";$f{$1}=$2; }
    return \%f;
}
sub native_hash {
    my($path)=@_;require_absolute($path);my $data=bytes($path);
    substr($data,0,4) eq "\x7fELF" or die "native ELF artifact required\n";
    return sha256_hex($data);
}
my $command=shift(@ARGV)//'';
if($command eq 'init') {
    @ARGV==9 or die "init source canonical ordered subsystem batch-size new-state-directory baseline-result backend reviewed-native-authority\n";
    my($source,$canonical,$ordered,$subsystem,$size,$root,$green,$backend,$authority_path)=@ARGV;
    $backend=~/\A(?:llvm|cranelift)\z/ or die "backend required\n";
    require_absolute($source,$canonical,$ordered,$root,$green,$authority_path);
    $size=~/\A[1-9][0-9]*\z/ or die "positive batch size required\n";
    !-e $root or die "state already exists\n";
    my $selection=product_selection($canonical,$ordered,$subsystem);
    my @owners=map {my @f=split /\t/; +{path=>$f[2],sha256=>$f[3]}} @{$selection->{rows}};
    for my $o(@owners) {sha256_hex(bytes("$source/$o->{path}")) eq $o->{sha256} or die "source changed\n";}
    my $g=read_json($green);my @accepted;
    my $authority=read_json($authority_path);
    $authority->{schema} eq 'simple-reviewed-native-authority-v1' && $authority->{backend} eq $backend &&
        $authority->{result_sha256} eq sha256_hex(bytes($green)) && length($authority->{reviewed_by}//'') &&
        $authority->{compiler_sha256}=~/\A[0-9a-f]{64}\z/ &&
        ($authority->{runtime_capsule_sha256}//'')=~/\A[0-9a-f]{64}\z/ &&
        sha256_hex(bytes($authority->{review_evidence})) eq $authority->{review_evidence_sha256} &&
        native_hash($authority->{compiler_path}) eq $authority->{compiler_sha256}
        or die "reviewed initial native authority mismatch\n";
    # Stable reviewed lane identity must match the initial build, not just
    # adjacent receipt labels. Old states without runtime authority are rejected.
    previous_build_evidence($green,$source,$authority->{compiler_sha256},
        $backend,$authority->{runtime_capsule_sha256});
    for my $variant(qw(positive negative)) {
        native_hash($authority->{variants}{$variant}{binary_path}) eq $authority->{variants}{$variant}{binary_sha256} &&
        $authority->{variants}{$variant}{binary_sha256} eq $g->{variants}{$variant}{binary_sha256}
            or die "initial native artifact differs\n";
    }
    if(($g->{schema}//'') eq 'simple-restricted-native-adapter-result-v1') {
        $g->{status} eq 'RESTRICTED_NATIVE_GATE_PASS' && !$g->{formal_product_pass} &&
            $g->{variants}{positive}{run_exit}==0 && $g->{variants}{negative}{run_exit}==1 &&
            $g->{variants}{positive}{source_sha256} eq $owners[0]{sha256}
            or die "invalid initial native gate\n";
        @accepted=($owners[0]{path});
    } else {
        die "initial baseline must be a verified native starter gate\n";
    }
    my @pending=map {$_->{path}} @owners;shift @pending;
    my $base={paths=>[ @accepted ],result=>$green,sha256=>sha256_hex(bytes($green))};
    my @queue; while(@pending) {push @queue,{phase=>"probe",added=>[splice(@pending,0,$size)],baseline=>$base};}
    save("$root/state.json",{schema=>'simple-native-batch-state-v2',backend=>$backend,source=>$source,subsystem=>$subsystem,
        canonical=>$canonical,canonical_sha256=>$selection->{canonical_inventory_sha256},
        native_authority=>$authority,native_authority_path=>$authority_path,native_authority_sha256=>sha256_hex(bytes($authority_path)),
        canonical_owners=>$selection->{canonical_subsystem_owner_count},ordered_sha256=>$selection->{spec_list_sha256},
        owners=>\@owners,accepted=>\@accepted,queue=>\@queue,quarantine=>[],trials=>[],decisions=>{},interactions=>[],
        baseline_result=>$green,baseline_result_sha256=>sha256_hex(bytes($green)),formal_product_pass=>JSON::PP::false});
    print "$root/state.json\n";exit;
}
@ARGV>=1 or die "expected next|record state-directory ...\n";
my $root=shift @ARGV;require_absolute($root);
mkdir "$root/writer.lock" or die "coordinator locked\n";
my $owns_lock=1;
END {rmdir "$root/writer.lock" if $owns_lock;}
my $s=read_json("$root/state.json");
$s->{schema} eq 'simple-native-batch-state-v2' or die "state migration required; preserve old evidence\n";
sha256_hex(bytes($s->{canonical})) eq $s->{canonical_sha256} or die "canonical inventory changed\n";
sub validate_pass {
    my($s,$request,$o)=@_;
    my $proof=$o->{verified_result}//die "missing verified native result\n";require_absolute($proof);
    my $g=read_json($proof);my $m=read_json(dirname($proof).'/manifest.json');
    # This trial grants union acceptance only for the exact pinned lane.
    # The shared validator binds result fields to strict, hash-bound build
    # evidence as well as independently reviewed producer/runtime identity.
    ($s->{native_authority}{runtime_capsule_sha256}//'')=~/\A[0-9a-f]{64}\z/
        or die "reviewed runtime authority missing; state migration required\n";
    previous_build_evidence($proof,$s->{source},$s->{native_authority}{compiler_sha256},
        $s->{backend},$s->{native_authority}{runtime_capsule_sha256});
    for my $variant(qw(positive negative)) {
        native_hash(dirname($proof)."/$variant.native") eq $g->{variants}{$variant}{binary_sha256}
            or die "native artifact differs from verified result\n";
    }
    # Restricted bridge has a strict verifier. New normal-framework receipt
    # schemas need an explicit reviewed validator before granting acceptance.
    $g->{schema} eq 'simple-restricted-prefix-result-v1' && $g->{status} eq 'RESTRICTED_PREFIX_GATE_PASS' &&
        !$g->{formal_product_pass} && $g->{detached_owners}==0 && $g->{quarantined_assertions}==0 &&
        $g->{compiled_owners}==@{$request->{selected}} && $g->{executed_owners}==@{$request->{selected}} &&
        $g->{manifest_sha256} eq sha256_hex(bytes(dirname($proof).'/manifest.json')) &&
        $m->{ordered_paths_sha256} eq $request->{ordered_paths_sha256} &&
        $m->{canonical_inventory_sha256} eq $s->{canonical_sha256} && $m->{source_root} eq $s->{source}
        or die "native result does not prove the whole trial selection\n";
    $o->{verified_result_sha256}=sha256_hex(bytes($proof));
}
sub apply_outcome {
    my($s,$request,$o,$path)=@_;
    my $action=queue_record($s,$request,$o);
    if($action eq 'QUARANTINE') {
        my $owner=$request->{added}[0];my($original)=grep {$_->{path} eq $owner} @{$s->{owners}};
        my $body=bytes("$s->{source}/$owner");sha256_hex($body) eq $original->{sha256} or die "quarantine source changed\n";
        write_bytes("$path/quarantine/original.spl",$body);
        write_bytes("$path/quarantine/retained-failure.spl","# QUARANTINED: see record.json for original source and diagnostics.\nfn main() -> i64:\n    assert(false)\n    1\n");
        my $q={path=>$owner,source_sha256=>$original->{sha256},status=>'SKIP',backend=>$s->{backend},
            scope=>'whole file rejected with original baseline; no unexecuted assertion claimed failed',
            original_baseline=>$request->{baseline}{paths},reason=>$o->{reason},failure_class=>$o->{failure_class},
            repair_owner=>$o->{repair_owner},evidence=>$o->{evidence},evidence_sha256=>$o->{evidence_sha256},
            original_source=>"$path/quarantine/original.spl",retained_fail_marker=>"$path/quarantine/retained-failure.spl",
            assertions=>'unknown; no passing or executed coverage claimed',restoration=>'pending'};
        save("$path/quarantine/record.json",$q);push @{$s->{quarantine}},$q;
    }
    return $action;
}
if($command eq 'next') {
    @ARGV==0 or die "next takes only state-directory\n";
    !$s->{active} or die "active trial requires explicit record; do not rerun\n";
    # Reuse a prior exact-selection decision without repeating native work.
    # Each reuse consumes/splits a finite task; cap protects corrupt state.
    my $limit=4*@{$s->{owners}}+10;
    while($limit--) {
        my $request=queue_request($s);
        if(!$request) {save("$root/state.json",$s);print "NO_PENDING_BATCHES: inspect exclusions and interactions; not a formal PASS\n";exit;}
        my $id=sprintf('trial-%04d',1+@{$s->{trials}});my $path="$root/$id";
        !-e $path or die "trial evidence already exists\n";
        $request->{id}=$id;$request->{schema}='simple-native-batch-request-v2';
        $request->{backend}=$s->{backend};$request->{source}=$s->{source};$request->{subsystem}=$s->{subsystem};
        $request->{canonical_inventory_sha256}=$s->{canonical_sha256};$request->{formal_product_pass}=JSON::PP::false;
        $request->{baseline_result}=$request->{baseline}{result};$request->{baseline_result_sha256}=$request->{baseline}{sha256};
        write_bytes("$path/ordered-paths.txt",join('',map {"$_\n"} @{$request->{selected}}));
        save("$path/request.json",$request);
        my $old=$s->{decisions}{$request->{ordered_paths_sha256}};
        if($old) {
            my $o=read_json($old->{outcome});
            sha256_hex(bytes($old->{outcome})) eq $old->{sha256} or die "prior outcome changed\n";
            if($o->{status} eq 'PASS') {validate_pass($s,$request,$o);}
            else {sha256_hex(bytes($o->{evidence})) eq $o->{evidence_sha256} or die "prior diagnostic changed\n";}
            $o->{reused_from}=$old->{outcome};
            my $action=apply_outcome($s,$request,$o,$path);
            save("$path/outcome.json",$o);push @{$s->{trials}},{id=>$id,status=>$o->{status},action=>$action,reused=>JSON::PP::true};
            save("$root/state.json",$s);next;
        }
        $s->{active}=$id;save("$root/state.json",$s);print "$path/request.json\n";exit;
    }
    die "bounded reuse limit exhausted; inspect state\n";
}
$command eq 'record' && @ARGV==1 or die "record state-directory outcome-json\n";
my $outcome_path=$ARGV[0];require_absolute($outcome_path);
my $id=$s->{active}//die "no active trial\n";my $path="$root/$id";
my $request=read_json("$path/request.json");my $o=read_json($outcome_path);
my $status=$o->{status}//'';
$status=~/\A(?:PASS|FAIL|BLOCKED)\z/ or die "invalid outcome\n";
sha256_hex(bytes("$path/ordered-paths.txt")) eq $request->{ordered_paths_sha256} or die "trial selection changed\n";
sha256_hex(bytes($request->{baseline_result})) eq $request->{baseline_result_sha256} or die "baseline receipt changed\n";
if($status eq 'PASS') {validate_pass($s,$request,$o);}
else {
    length($o->{reason}//'') && length($o->{repair_owner}//'') or die "reason and repair owner required\n";
    require_absolute($o->{evidence}//'');my $data=bytes($o->{evidence});length($data) or die "empty failure evidence\n";
    $o->{evidence_sha256}=sha256_hex($data);
    $status ne 'FAIL' || ($o->{failure_class}//'')=~/\A(?:compile|link|assertion)\z/
        or die "infrastructure/unsupported adapter is BLOCKED, not an assertion failure\n";
}
my $action=apply_outcome($s,$request,$o,$path);
save("$path/outcome.json",$o);
$s->{decisions}{$request->{ordered_paths_sha256}}={outcome=>"$path/outcome.json",sha256=>sha256_hex(bytes("$path/outcome.json"))};
push @{$s->{trials}},{id=>$id,status=>$status,action=>$action,added=>$request->{added}};
delete $s->{active};save("$root/state.json",$s);
print "action=$action accepted=",scalar(@{$s->{accepted}}),'/', $s->{canonical_owners},' quarantined=',scalar(@{$s->{quarantine}}),
    ' interactions=',scalar(@{$s->{interactions}}),' pending_batches=',scalar(@{$s->{queue}})," formal_product_pass=false\n";
