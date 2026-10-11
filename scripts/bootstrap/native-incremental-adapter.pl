#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use BootstrapProductSelection qw(product_selection);
use Digest::SHA qw(sha256_hex);
use JSON::PP;
use File::Path qw(make_path);
use File::Basename qw(dirname);

# Closed, source-bound scalar equality lane. General framework execution remains
# separate; unsupported owners are retained as detached, never silently passed.
@ARGV == 6 or die "expected source-root canonical-inventory ordered-list subsystem new-output previous-manifest-or-dash\n";
my ($root,$canonical,$list,$subsystem,$out,$previous) = @ARGV;
for ($root,$out) { m{\A/} && !/[\r\n\0]/ or die "absolute paths required\n"; }
sub bytes {
    my ($path) = @_;
    -f $path && !-l $path or die "missing or linked input: $path\n";
    open my $f,'<:raw',$path or die $!; local $/; return <$f>;
}
sub write_bytes {
    my ($path,$value)=@_; make_path(dirname($path));
    open my $f,'>:raw',$path or die $!; print {$f} $value; close $f or die $!;
}
sub quoted {
    my ($value)=@_; $value !~ /["\\\r\n\0{}]/ or die "unsupported declaration text\n";
    return $value;
}
my $json=JSON::PP->new->canonical->pretty;
my $selection=product_selection($canonical,$list,$subsystem);
my @paths=map { (split /\t/)[2] } @{$selection->{rows}};
my $prior;
if ($previous eq '-') { @paths==1 or die "initial prefix must select exactly one owner\n"; }
else {
    $prior=decode_json(bytes($previous));
    $prior->{schema} eq 'simple-restricted-prefix-v1' && $prior->{source_root} eq $root &&
        $prior->{subsystem} eq $subsystem && $prior->{canonical_inventory_sha256} eq $selection->{canonical_inventory_sha256}
        or die "prefix lineage differs\n";
    @paths == @{$prior->{ordered_paths}}+1 or die "append exactly one owner\n";
    for my $i (0..$#paths-1) { $paths[$i] eq $prior->{ordered_paths}[$i] or die "prefix order changed\n"; }
}
my $catalog_bytes=bytes("$FindBin::Bin/fixtures/native-incremental-adapter-catalog.json");
my $catalog=decode_json($catalog_bytes);
my %approved=map { $_->{path}=>$_ } @{$catalog->{owners}};
my (@owners,@cases,%source);
for my $row (@{$selection->{rows}}) {
    my (undef,undef,$path,$sha)=split /\t/,$row;
    my $body=bytes("$root/$path"); sha256_hex($body) eq $sha or die "canonical source changed: $path\n";
    $source{$path}=$body;
    my $entry={path=>$path,source_sha256=>$sha}; push @owners,$entry;
    if (!exists($approved{$path}) || $approved{$path}{sha256} ne $sha) {
        $entry->{attachment}='detached'; $entry->{reason}='adapter has no reviewed lowering for this exact source';
        $entry->{evidence}="sources/$path"; $entry->{cases}=undef; $entry->{assertions}=undef;
        next;
    }
    my ($describe,$current); my @file_cases;
    my @lines=split /\n/,$body;
    for my $i (0..$#lines) {
        my $line=$lines[$i];
        if ($line =~ /^describe "([^"]+)":$/) { !defined($describe) or die "multiple describes unsupported\n"; $describe=quoted($1); next; }
        if ($line =~ /^    it "([^"]+)":$/) {
            defined($describe) or die "case outside describe\n";
            $current={owner=>$path,describe=>$describe,name=>quoted($1),body=>[],assertions=>[],
                id=>sha256_hex(join("\0",'restricted-prefix-case-v1',$path,$describe,$1)),scalar_type=>$approved{$path}{scalar_type}};
            push @file_cases,$current; next;
        }
        next if $line eq '';
        defined($current) && $line =~ /^        / or die "unrecognized authored line $path:".($i+1)."\n";
        if ($line =~ /^        expect\((.+)\)\.to_equal\((.+)\)$/) {
            my ($actual,$expected)=($1,$2);
            my $type=$current->{scalar_type};
            $expected =~ ($type eq 'bool' ? qr/\A(?:true|false)\z/ : qr/\A-?\d+(?:\.\d+)?\z/)
                or die "unsupported expected scalar\n";
            my $assertion={line=>$i+1,actual=>$actual,expected=>$expected,original=>$line};
            push @{$current->{assertions}},$assertion; push @{$current->{body}},{assertion=>$assertion};
        } else {
            $line =~ s/^    //; push @{$current->{body}},{line=>$i+1,code=>$line};
        }
    }
    my $assertions=0; $assertions+=@{$_->{assertions}} for @file_cases;
    @file_cases==$approved{$path}{case_count} && $assertions==$approved{$path}{assertion_count}
        or die "reviewed case/assertion count differs\n";
    $entry->{attachment}='attached'; $entry->{cases}=scalar(@file_cases);$entry->{assertions}=$assertions;
    push @cases,@file_cases;
}
@cases or die "no supported attached cases; no native entry produced\n";
my @new_cases=grep { $_->{owner} eq $paths[-1] } @cases;
my $negative_case=@new_cases ? $new_cases[0] : undef;
my $negative_line=$negative_case ? $negative_case->{assertions}[0]{line} : undef;
!-e $out && !-l $out or die "output exists; retain prior evidence\n";
make_path($out);
write_bytes("$out/ordered-paths.txt",bytes($list));
write_bytes("$out/canonical-inventory.tsv",bytes($canonical));
write_bytes("$out/sources/$_",$source{$_}) for @paths;
my $proof={schema=>'simple-restricted-prefix-v1',source_root=>$root,subsystem=>$subsystem,
    canonical_inventory_sha256=>$selection->{canonical_inventory_sha256},canonical_owners=>$selection->{canonical_subsystem_owner_count},
    ordered_paths=>\@paths,ordered_paths_sha256=>$selection->{spec_list_sha256},
    catalog_sha256=>sha256_hex($catalog_bytes),owners=>\@owners,
    selected_owners=>scalar(@paths),attached_owners=>scalar(grep {$_->{attachment} eq 'attached'} @owners),
    detached_owners=>scalar(grep {$_->{attachment} eq 'detached'} @owners),compiled_owners=>0,executed_owners=>0,
    quarantined_assertions=>0,formal_product_pass=>JSON::PP::false,
    previous_manifest_sha256=>($previous eq '-' ? undef : sha256_hex(bytes($previous))),
    negative_control_available=>($negative_case?JSON::PP::true:JSON::PP::false)};
for my $variant (qw(positive negative)) {
    next if $variant eq 'negative' && !$negative_case;
    my $entry="use std.sffi.cli_args.{cli_get_args}\n\n";
    my (@mapping,@case_proofs,%variant_sources);
    for my $case (@cases) {
        my $fn='case_'.$case->{id}; my $assertions=@{$case->{assertions}};
        $entry.="fn $fn() -> i64:\n    var adapter_assertions: i64 = 0\n    var adapter_failures: i64 = 0\n";
        my @checks;
        for my $item (@{$case->{body}}) {
            my $start=1+($entry =~ tr/\n/\n/);
            if (exists($item->{code})) {
                $entry.="$item->{code}\n";
                push @mapping,{owner=>$case->{owner},original_line=>$item->{line},generated_first_line=>$start,action=>'unchanged body; wrapper indentation only'};
                next;
            }
            my $a=$item->{assertion};my $expected=$a->{expected};
            my $mutated=$variant eq 'negative' && $case->{id} eq $negative_case->{id} && $a->{line}==$negative_line;
            if ($mutated) {
                $expected=$case->{scalar_type} eq 'bool' ? ($expected eq 'true'?'false':'true') : $expected+1;
                $expected.='.0' if $case->{scalar_type} eq 'f64' && $expected !~ /\./;
                my @lines=split /\n/,$source{$case->{owner}};
                $lines[$a->{line}-1]="        expect($a->{actual}).to_equal($expected)";
                $variant_sources{$case->{owner}}=join("\n",@lines)."\n";
            }
            my $index=1+@checks; my $type=$case->{scalar_type};
            $entry.="    val adapter_actual_$index: $type = $a->{actual}\n    val adapter_expected_$index: $type = $expected\n";
            $entry.="    adapter_assertions = adapter_assertions + 1\n    if adapter_actual_$index != adapter_expected_$index:\n        adapter_failures = adapter_failures + 1\n";
            for my $status (qw(FAIL PASS)) {
                $entry.="    else:\n" if $status eq 'PASS';
                $entry.='        print "assertion\\tcase='.$case->{id}.'\\tline='.$a->{line}.'\\tstatus='.$status.'\\tactual={adapter_actual_'.$index.'}\\texpected={adapter_expected_'.$index.'}"'."\n";
            }
            push @checks,{line=>$a->{line},scalar_type=>$type,expected_actual=>$a->{expected},expected=>$expected,status=>($mutated?'FAIL':'PASS')};
            push @mapping,{owner=>$case->{owner},original_line=>$a->{line},original_assertion=>$a->{original},generated_first_line=>$start,
                action=>'evaluate each actual and expected exactly once; compare typed scalar'};
        }
        $entry.="    if adapter_assertions != $assertions: return 125\n    if adapter_failures > 0:\n";
        $entry.='        print "result\\t'.$case->{id}.'\\tFAIL\\tassertions={adapter_assertions}\\tfailures={adapter_failures}"'."\n        return 1\n";
        $entry.='    print "result\\t'.$case->{id}.'\\tPASS\\tassertions={adapter_assertions}\\tfailures=0"'."\n    0\n\n";
        push @case_proofs,{id=>$case->{id},owner=>$case->{owner},describe=>$case->{describe},name=>$case->{name},assertions=>\@checks};
    }
    $entry.="fn main() -> i64:\n    var enumerating = false\n    var running = false\n    for arg in cli_get_args():\n        if arg == \"--enumerate\": enumerating = true\n        elif arg == \"--run\": running = true\n    if enumerating == running: return 2\n";
    my @variant_owners;
    for my $owner (grep {$_->{attachment} eq 'attached'} @owners) {
        my $path=$owner->{path};my $body=$variant_sources{$path}//$source{$path};my $sha=sha256_hex($body);
        write_bytes("$out/$variant-sources/$path",$body);
        push @variant_owners,{path=>$path,sha256=>$sha};
        $entry.='    print "owner\\t'.$path.'\\t'.$sha.'"'."\n";
    }
    for my $case (@cases) {$entry.='    print "declare\\t'.$case->{id}.'\\t'.$case->{describe}.'\\t'.$case->{name}.'"'."\n";}
    $entry.="    if enumerating:\n        print \"enumeration-complete\\tcases=".scalar(@cases)."\"\n        return 0\n    var failed_cases: i64 = 0\n";
    for my $case (@cases) {$entry.="    val result_$case->{id} = case_$case->{id}()\n    if result_$case->{id} == 125: return 125\n    if result_$case->{id} != 0: failed_cases = failed_cases + 1\n";}
    $entry.="    if failed_cases > 0: return 1\n    0\n";
    write_bytes("$out/$variant-entry.spl",$entry);write_bytes("$out/$variant-line-map.json",$json->encode(\@mapping));
    $proof->{variants}{$variant}={entry_sha256=>sha256_hex($entry),owners=>\@variant_owners,cases=>\@case_proofs,
        expected_exit=>($variant eq 'positive'?0:1)};
}
write_bytes("$out/manifest.json",$json->encode($proof));
print "selected=$proof->{selected_owners} attached=$proof->{attached_owners} detached=$proof->{detached_owners} compiled=0 executed=0\n";
