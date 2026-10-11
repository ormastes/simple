#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use JSON::PP;
@ARGV == 1 or die "expected evidence directory\n";
my ($root) = @ARGV;
sub bytes {
    my ($name) = @_;
    -f "$root/$name" && !-l "$root/$name" or die "missing or linked evidence: $name\n";
    open my $f, '<:raw', "$root/$name" or die $!;
    local $/; return <$f>;
}
my $proof = decode_json(bytes('provenance.json'));
my $owner = 'test/01_unit/compiler/interpreter/while_body_scope_spec.spl';
my $case = '858157aa34c088cf0ea8171ae89401567d5f5fe487fd9fafa89b769f5b8bc1da';
my $original = '492ce803161d0df2b2b21fa540f154f15b8d82aa0156698700502596eb6f985f';
$proof->{owner} eq $owner && $proof->{case_id} eq $case && $proof->{original_sha256} eq $original
    && !$proof->{formal_product_pass} && !$proof->{stdlib_framework_pass}
    or die "adapter identity differs\n";
my %result = (schema=>'simple-restricted-native-adapter-result-v1',
    status=>'RESTRICTED_NATIVE_GATE_PASS', formal_product_pass=>JSON::PP::false,
    stdlib_framework_pass=>JSON::PP::false, source_files=>1, cases=>1, assertions=>2);
for my $variant (qw(positive negative)) {
    my $sha = sha256_hex(bytes("$variant-source.spl"));
    my $expected_sha = $variant eq 'positive' ? $original : '2a6adb94de096901ed4c89438f5a26295e79eae2e886cd9bf68450d17a52de32';
    my $entry_sha = $variant eq 'positive' ? '87d1c51dd80305e1b52c277f5e465a75a0553510221ff081114f65210ced5442'
        : '1809eabd3a74c2a5b238da7bc63e21ea1dcfc6f517e27589b31786225967e903';
    $sha eq $expected_sha && $sha eq $proof->{variants}{$variant}{source_sha256}
        && sha256_hex(bytes("$variant-entry.spl")) eq $entry_sha
        && $entry_sha eq $proof->{variants}{$variant}{entry_sha256} or die "source/entry binding differs\n";
    my $binary = bytes($variant);
    substr($binary,0,4) eq "\x7fELF" or die "expected actual native ELF image\n";
    my $prefix = "owner\t$owner\t$sha\n";
    $prefix .= "variant\tnegative-control\toriginal-source-sha=$original\tvariant-source-sha=$sha\n" if $variant eq 'negative';
    $prefix .= "declare\t$case\tinterpreter while-body scope\tdoes not overwrite an enclosing binding\n";
    for my $mode (qw(enumerate run)) {
        my ($expected, $exit) = ($prefix, 0);
        if ($mode eq 'enumerate') { $expected .= "enumeration-complete\tcases=1\n"; }
        else {
            my ($state,$value,$failures) = $variant eq 'positive' ? ('PASS',2,0) : ('FAIL',3,1);
            $exit = $failures;
            $expected .= "assertion\tline=8\tstatus=$state\tactual=2\texpected=$value\n";
            $expected .= "assertion\tline=9\tstatus=PASS\tactual=99\texpected=99\n";
            $expected .= "result\t$case\t$state\tassertions=2\tfailures=$failures\n";
        }
        bytes("$variant-$mode.stdout.log") eq $expected && bytes("$variant-$mode.stderr.log") eq ''
            && bytes("$variant-$mode.exit") eq "$exit\n" or die "$variant $mode execution differs\n";
    }
    $result{variants}{$variant} = {binary_sha256=>sha256_hex($binary), source_sha256=>$sha, entry_sha256=>$entry_sha,
        run_exit=>($variant eq 'positive'?0:1)};
}
print JSON::PP->new->canonical->pretty->encode(\%result);
