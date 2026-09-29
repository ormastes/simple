#!/usr/bin/env perl
use strict;
use warnings;
use JSON::PP ();

sub reject {
    my ($status, $reason) = @_;
    print STDERR "validate-jest-json: $reason\n";
    exit $status;
}

@ARGV == 1 or reject(91, 'expected one JSON result path');
open my $fh, '<:raw', $ARGV[0] or reject(91, 'cannot read JSON result');
local $/;
my $raw = <$fh>;
close $fh or reject(91, 'cannot close JSON result');
defined($raw) && length($raw) or reject(91, 'empty JSON result');

my $decoded = eval { JSON::PP::decode_json($raw) };
reject(91, 'malformed or truncated JSON') if $@ || ref($decoded) ne 'HASH';
for my $key (qw(success numPassedTests numFailedTests numPendingTests)) {
    my $occurrences = () = $raw =~ /(?<!\\)"\Q$key\E"\s*:/g;
    $occurrences == 1 or reject(91, "ambiguous $key field");
    exists $decoded->{$key} or reject(91, "missing $key");
}
JSON::PP::is_bool($decoded->{success}) or reject(91, 'success is not boolean');
my @counts;
for my $key (qw(numPassedTests numFailedTests numPendingTests)) {
    my $value = $decoded->{$key};
    defined($value) && !ref($value) && "$value" =~ /\A(?:0|[1-9][0-9]{0,8})\z/
        or reject(91, "$key is not a bounded nonnegative integer");
    push @counts, 0 + $value;
}
my ($passed, $failed, $skipped) = @counts;
print "$passed\t$failed\t$skipped\n";
exit 93 if !$decoded->{success} || $failed != 0;
exit 92 if $passed + $failed == 0;
