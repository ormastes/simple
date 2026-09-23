#!/usr/bin/env perl
use strict;
use warnings;
use JSON::PP ();

sub reject {
    my ($status, $reason) = @_;
    print STDERR "validate-test-runner-json: $reason\n";
    exit $status;
}

@ARGV == 1 or reject(91, 'expected one JSON log path');
open my $fh, '<:raw', $ARGV[0] or reject(91, 'cannot read JSON log');
my @rows;
while (my $line = <$fh>) {
    $line =~ s/\r?\n\z//;
    push @rows, $line if $line =~ /^\{"success":/;
}
close $fh or reject(91, 'cannot close JSON log');
@rows == 1 or reject(91, 'expected exactly one terminal JSON row');
my $row = $rows[0];

my $decoded = eval { JSON::PP::decode_json($row) };
reject(91, 'malformed or truncated JSON') if $@ || ref($decoded) ne 'HASH';
join(',', sort keys %{$decoded}) eq 'sdoctest,spec,spl_doctest,success'
    or reject(91, 'outer JSON key set is not canonical');
JSON::PP::is_bool($decoded->{success}) or reject(91, 'outer success is not boolean');
ref($decoded->{spec}) eq 'HASH' or reject(91, 'spec result is absent');
defined($decoded->{spl_doctest}) and reject(91, 'unexpected SPL doctest result');
defined($decoded->{sdoctest}) and reject(91, 'unexpected sdoctest result');

my $spec = $decoded->{spec};
join(',', sort keys %{$spec}) eq
    'files,groups,success,total_duration_ms,total_failed,total_passed,total_pending,total_skipped'
    or reject(91, 'spec JSON key set is not canonical');
JSON::PP::is_bool($spec->{success}) or reject(91, 'spec success is not boolean');
ref($spec->{groups}) eq 'ARRAY' or reject(91, 'groups is not an array');
ref($spec->{files}) eq 'ARRAY' or reject(91, 'files is not an array');

my %structural_key_count;
for (my $i = 0; $i < length($row); $i++) {
    next if substr($row, $i, 1) ne '"';
    my $start = $i;
    $i++;
    my $escaped = 0;
    while ($i < length($row)) {
        my $char = substr($row, $i, 1);
        if ($escaped) {
            $escaped = 0;
        } elsif ($char eq '\\') {
            $escaped = 1;
        } elsif ($char eq '"') {
            last;
        }
        $i++;
    }
    $i < length($row) or reject(91, 'unterminated JSON string');
    my $after = $i + 1;
    $after++ while $after < length($row) && substr($row, $after, 1) =~ /\s/;
    next if $after >= length($row) || substr($row, $after, 1) ne ':';
    my $key_token = substr($row, $start, $i - $start + 1);
    my $key = eval { JSON::PP::decode_json($key_token) };
    reject(91, 'malformed JSON object key') if $@ || ref($key);
    $structural_key_count{$key}++;
}
for my $key (qw(total_passed total_failed total_skipped total_pending total_duration_ms)) {
    ($structural_key_count{$key} // 0) == 1
        or reject(91, "ambiguous $key field");
}
($structural_key_count{success} // 0) == 2
    or reject(91, 'ambiguous success field');

my $count = qr/(?:0|[1-9][0-9]{0,8})/;
$row =~ /\A\{"success":(true|false),"spec":\{"success":(true|false),"total_passed":($count),"total_failed":($count),"total_skipped":($count),"total_pending":($count),"total_duration_ms":($count),"groups":/
    or reject(91, 'noncanonical or oversized spec counters');
my ($outer_success, $spec_success, $passed, $failed, $skipped, $pending, $duration) =
    ($1, $2, $3, $4, $5, $6, $7);
$row =~ /,"spl_doctest":null,"sdoctest":null\}\z/
    or reject(91, 'terminal JSON suffix is incomplete or noncanonical');

($outer_success eq ($decoded->{success} ? 'true' : 'false'))
    or reject(91, 'decoded outer success differs');
($spec_success eq ($spec->{success} ? 'true' : 'false'))
    or reject(91, 'decoded spec success differs');
$spec->{total_passed} == $passed or reject(91, 'decoded passed count differs');
$spec->{total_failed} == $failed or reject(91, 'decoded failed count differs');
$spec->{total_skipped} == $skipped or reject(91, 'decoded skipped count differs');
$spec->{total_pending} == $pending or reject(91, 'decoded pending count differs');
$spec->{total_duration_ms} == $duration or reject(91, 'decoded duration differs');
print "$passed\t$failed\t$skipped\n";
exit 93 if $outer_success eq 'false' || $spec_success eq 'false' || $failed != 0;
exit 92 if $passed + $failed == 0;
