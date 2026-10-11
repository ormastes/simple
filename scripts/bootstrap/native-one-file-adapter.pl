#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use Digest::SHA qw(sha256_hex);
use JSON::PP;
use File::Path qw(make_path);

# A deliberately closed compatibility adapter, not a general BDD translator.
# Refuse changed source rather than silently dropping an unsupported assertion.
my ($root, $out) = @ARGV;
@ARGV == 2 && $root =~ m{\A/} && $out =~ m{\A/}
    or die "usage: native-one-file-adapter.pl ABS_SOURCE_ROOT ABS_NEW_OUTPUT\n";
my $owner = 'test/01_unit/compiler/interpreter/while_body_scope_spec.spl';
my $original_sha = '492ce803161d0df2b2b21fa540f154f15b8d82aa0156698700502596eb6f985f';
my $case = '858157aa34c088cf0ea8171ae89401567d5f5fe487fd9fafa89b769f5b8bc1da';
sub read_bytes {
    my ($path) = @_;
    -f $path && !-l $path or die "missing or linked input: $path\n";
    open my $f, '<:raw', $path or die $!;
    local $/; return <$f>;
}
sub write_bytes {
    my ($path, $bytes) = @_;
    open my $f, '>:raw', $path or die $!;
    print {$f} $bytes; close $f or die $!;
}
my $source = read_bytes("$root/$owner");
sha256_hex($source) eq $original_sha or die "unsupported source bytes; no cases adapted\n";
my $entry = read_bytes("$FindBin::Bin/fixtures/native-while-scope-adapter.spl");
sha256_hex($entry) eq '87d1c51dd80305e1b52c277f5e465a75a0553510221ff081114f65210ced5442'
    or die "unreviewed adapter template\n";
!-e $out && !-l $out or die "output already exists; preserve prior evidence\n";
my @source_lines = split /\n/, $source;
my @entry_lines = split /\n/, $entry;
my @mapping;
for my $line (1 .. 9) {
    if ($line <= 2) {
        push @mapping, {original_line=>$line, action=>'BDD declaration represented by stable enumerated case identity'};
    } elsif ($line <= 7) {
        my $body = $source_lines[$line-1];
        $body =~ s/^    // or die "unexpected body indentation\n";
        $body eq $entry_lines[$line+2] or die "authored body changed\n";
        push @mapping, {original_line=>$line, generated_first_line=>$line+3,
            generated_last_line=>$line+3, action=>'authored body retained with wrapper indentation removed'};
    } else {
        push @mapping, {original_line=>$line, generated_first_line=>($line==8?11:17),
            generated_last_line=>($line==8?16:22), action=>'real integer equality; failure increments runtime counter'};
    }
}
my $json = JSON::PP->new->canonical->pretty;
my %proof = (schema=>'simple-restricted-native-adapter-v1', owner=>$owner,
    original_sha256=>$original_sha, case_id=>$case, source_root=>$root,
    formal_product_pass=>JSON::PP::false, stdlib_framework_pass=>JSON::PP::false,
    assertions_lowered=>2, source_files=>1, supported_shape=>'exact while_body_scope source only');
make_path($out);
for my $variant (qw(positive negative)) {
    my ($body, $generated) = ($source, $entry);
    if ($variant eq 'negative') {
        $body =~ s/expect\(i\)\.to_equal\(2\)/expect(i).to_equal(3)/ == 1 or die "mutation missing\n";
        $generated =~ s/if i != 2:/if i != 3:/ == 1 or die "comparison missing\n";
        $generated =~ s/expected=2/expected=3/g == 2 or die "comparison evidence missing\n";
        my $sha = sha256_hex($body);
        $generated =~ s/\Q$original_sha\E/$sha/ == 1 or die "owner missing\n";
        $generated =~ s/(    print "declare)/    print "variant\\tnegative-control\\toriginal-source-sha=$original_sha\\tvariant-source-sha=$sha"\n$1/ == 1
            or die "declaration missing\n";
    }
    write_bytes("$out/$variant-source.spl", $body);
    write_bytes("$out/$variant-entry.spl", $generated);
    write_bytes("$out/$variant-line-map.json", $json->encode(\@mapping));
    $proof{variants}{$variant} = {source_sha256=>sha256_hex($body), entry_sha256=>sha256_hex($generated)};
}
write_bytes("$out/provenance.json", $json->encode(\%proof));
print "generated exact one-file adapter; formal product qualification: false\n";
