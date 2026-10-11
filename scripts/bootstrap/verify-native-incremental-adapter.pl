#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/lib";
use NativeAdapterEvidence qw(build_evidence);
use Digest::SHA qw(sha256_hex);
use JSON::PP;
@ARGV==2 or die "expected prefix evidence directory and live binary directory\n";
my ($root,$binary_root)=@ARGV;
sub bytes {my ($name)=@_;-f "$root/$name" && !-l "$root/$name" or die "missing/linked $name\n";open my $f,'<:raw',"$root/$name" or die $!;local $/;return <$f>;}
my $p=decode_json(bytes('manifest.json'));
my $build_evidence=build_evidence($root,0);
$build_evidence->{workspace} eq $p->{source_root} or die "build source workspace differs\n";
$p->{schema} eq 'simple-restricted-prefix-v1' && !$p->{formal_product_pass} && $p->{negative_control_available}
    or die "prefix has no positive/negative native authority\n";
sha256_hex(bytes('canonical-inventory.tsv')) eq $p->{canonical_inventory_sha256} &&
    sha256_hex(bytes('ordered-paths.txt')) eq $p->{ordered_paths_sha256} or die "selection changed\n";
for my $owner (@{$p->{owners}}) {sha256_hex(bytes("sources/$owner->{path}")) eq $owner->{source_sha256} or die "original source changed\n";}
my $result={schema=>'simple-restricted-prefix-result-v1',status=>'RESTRICTED_PREFIX_GATE_PASS',formal_product_pass=>JSON::PP::false,
    manifest_sha256=>sha256_hex(bytes('manifest.json')),selected_owners=>$p->{selected_owners},attached_owners=>$p->{attached_owners},
    compiled_owners=>$p->{attached_owners},executed_owners=>$p->{attached_owners},detached_owners=>$p->{detached_owners},quarantined_assertions=>0,
    %$build_evidence};
for my $variant (qw(positive negative)) {
    my $v=$p->{variants}{$variant};sha256_hex(bytes("$variant-entry.spl")) eq $v->{entry_sha256} or die "entry changed\n";
    my $prefix='';
    for my $o (@{$v->{owners}}) {
        sha256_hex(bytes("$variant-sources/$o->{path}")) eq $o->{sha256} or die "variant source changed\n";
        $prefix.="owner\t$o->{path}\t$o->{sha256}\n";
    }
    for my $c (@{$v->{cases}}) {$prefix.="declare\t$c->{id}\t$c->{describe}\t$c->{name}\n";}
    my $run=$prefix;my $failed_cases=0;my $assertions=0;
    for my $c (@{$v->{cases}}) {
        my $failures=0;
        for my $a (@{$c->{assertions}}) {
            $assertions++;$failures++ if $a->{status} eq 'FAIL';
            # All admitted expected literals are scalar; normalize native float
            # formatting numerically below, while retaining full line structure.
            $run.="assertion\tcase=$c->{id}\tline=$a->{line}\tstatus=$a->{status}\tactual=$a->{expected_actual}\texpected=$a->{expected}\n";
        }
        $failed_cases++ if $failures;
        $run.="result\t$c->{id}\t".($failures?'FAIL':'PASS')."\tassertions=".scalar(@{$c->{assertions}})."\tfailures=$failures\n";
    }
    ($variant eq 'positive' ? $failed_cases==0 : $failed_cases==1) or die "negative mutation count differs\n";
    for my $mode (qw(enumerate run)) {
        my $expected=$mode eq 'run'?$run:$prefix.'enumeration-complete' . "\tcases=".scalar(@{$v->{cases}})."\n";
        my $observed=bytes("$variant-$mode.stdout.log");
        # Exact transcripts for bool/i64. F64 equalities retain numeric checks
        # despite backend-specific shortest decimal output (1 versus 1.0).
        my @want=split /\n/,$expected;my @got=split /\n/,$observed;
        @want==@got && $observed=~/\n\z/ or die "transcript line count differs\n";
        for my $i (0..$#want) {
            next if $want[$i] eq $got[$i];
            $want[$i]=~/\A(assertion\tcase=([0-9a-f]+)\tline=(\d+)\tstatus=\w+\tactual=)(-?\d+(?:\.\d+)?)\texpected=(-?\d+(?:\.\d+)?)\z/ or die "transcript differs\n";
            my ($head,$id,$line,$actual,$expected_value)=($1,$2,$3,$4,$5);
            my @match=map {@{$_->{assertions}}} grep {$_->{id} eq $id} @{$v->{cases}};
            my ($a)=grep {$_->{line}==$line} @match;
            $a && $a->{scalar_type} eq 'f64' or die "non-float transcript differs\n";
            $got[$i]=~/\A\Q$head\E(-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\texpected=(-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\z/
                && 0+$1==0+$actual && 0+$2==0+$expected_value or die "float comparison evidence differs\n";
        }
        my $exit=$mode eq 'enumerate'?0:$v->{expected_exit};
        bytes("$variant-$mode.stderr.log") eq '' && bytes("$variant-$mode.exit") eq "$exit\n" or die "execution status differs\n";
    }
    my $build=decode_json(bytes("$variant-binary.json"));
    $build->{native_format} eq 'ELF' && $build->{sha256}=~/\A[0-9a-f]{64}\z/ or die "native binary receipt missing\n";
    my $path="$binary_root/latest-$variant";
    -f $path && !-l $path or die "live native artifact unavailable\n";
    open my $binary,'<:raw',$path or die $!; my $magic; read($binary,$magic,4)==4 && $magic eq "\x7fELF" or die "not a native ELF image\n";
    seek($binary,0,0);my $hash=Digest::SHA->new(256);$hash->addfile($binary);
    $hash->hexdigest eq $build->{sha256} or die "live native artifact no longer matches historical receipt\n";
    $result->{variants}{$variant}={binary_sha256=>$build->{sha256},entry_sha256=>$v->{entry_sha256},cases=>scalar(@{$v->{cases}}),assertions=>$assertions,exit=>$v->{expected_exit}};
}
print JSON::PP->new->canonical->pretty->encode($result);
