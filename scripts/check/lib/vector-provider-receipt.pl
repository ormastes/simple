#!/usr/bin/env perl
use strict;
use warnings;
use Math::BigInt;

sub fail { die "vector-provider-receipt: $_[0]\n"; }

@ARGV >= 2 or fail('usage: receipt.pl FILE EXPECTED_PID [--no-load] [--require-load] [--require-op=N:MIN_EVENTS:MIN_LOOPS] [--exact-op=N:EVENTS:LOOPS] [--success-only-op=N] [--forbid-op=N]');
my ($path, $expected_pid) = splice(@ARGV, 0, 2);
$expected_pid =~ /\A[1-9][0-9]*\z/ or fail('invalid expected PID');
my $no_load = 0;
my $require_load = 0;
my @require_ops;
my @exact_ops;
my @success_only_ops;
my @forbidden_ops;
for my $arg (@ARGV) {
    if ($arg eq '--no-load') { $no_load = 1; next; }
    if ($arg eq '--require-load') { $require_load = 1; next; }
    if ($arg =~ /\A--require-op=([1-4]):([1-9][0-9]*):([1-9][0-9]*)\z/) {
        push @require_ops, [map { Math::BigInt->new($_) } ($1, $2, $3)];
        next;
    }
    if ($arg =~ /\A--exact-op=([1-4]):([0-9]+):([0-9]+)\z/) {
        push @exact_ops, [map { Math::BigInt->new($_) } ($1, $2, $3)];
        next;
    }
    if ($arg =~ /\A--success-only-op=([1-4])\z/) { push @success_only_ops, 0 + $1; next; }
    if ($arg =~ /\A--forbid-op=([1-4])\z/) { push @forbidden_ops, 0 + $1; next; }
    fail("invalid expectation $arg");
}

my $max = Math::BigInt->new('18446744073709551615');
open my $fh, '<:raw', $path or fail('receipt open failed');
my $bytes = '';
while (length($bytes) <= 4096) {
    my $chunk = '';
    my $read = read($fh, $chunk, 4097 - length($bytes));
    defined $read or fail('receipt read failed');
    last if $read == 0;
    $bytes .= $chunk;
}
close $fh or fail('receipt close failed');
length($bytes) <= 4096 or fail('receipt exceeds bound');
$bytes =~ /\n\z/ or fail('receipt missing final newline');
my @lines = split /\n/, $bytes, -1;
pop @lines if @lines && $lines[-1] eq '';
@lines == 38 or fail('receipt field count mismatch');
shift(@lines) eq 'SIMPLE_VECTOR_TEST_EVENTS_V1' or fail('receipt header mismatch');
my %values;
for my $line (@lines) {
    $line =~ /\A([a-z0-9_]+)=([0-9]+)\z/ or fail('malformed receipt field');
    exists $values{$1} and fail('duplicate receipt key');
    length($2) <= 20 or fail('receipt integer width exceeds u64');
    my $number = Math::BigInt->new($2);
    $number <= $max or fail('receipt integer exceeds u64');
    $values{$1} = $number;
}
my @expected = qw(pid loads events malformed overflow);
for my $op (1..4) {
    push @expected, "op${op}_loops";
    push @expected, map { "op${op}_status$_" } 0..6;
}
keys(%values) == @expected or fail('receipt has missing or extra fields');
for my $key (@expected) { exists $values{$key} or fail("missing field $key"); }
$values{pid}->bstr eq $expected_pid or fail('receipt PID mismatch');
$values{loads} <= Math::BigInt->new(1) or fail('multiple provider loads');
$values{malformed}->is_zero or fail('malformed callback event');
$values{overflow}->is_zero or fail('observer counter overflow');
my %op_total;
my $event_sum = Math::BigInt->new(0);
for my $op (1..4) {
    my $successes = $values{"op${op}_status0"};
    my $op_sum = Math::BigInt->new(0);
    for my $status (0..6) { $op_sum->badd($values{"op${op}_status$status"}); }
    $op_total{$op} = $op_sum;
    $event_sum->badd($op_sum);
    $values{"op${op}_loops"}->is_zero || !$successes->is_zero
        or fail("loop count without a successful event for op $op");
}
$event_sum->bstr eq $values{events}->bstr or fail('status counts do not sum to event count');
if ($no_load) {
    $values{loads}->is_zero && $values{events}->is_zero or fail('expected no provider load or event');
    for my $op (1..4) {
        $op_total{$op}->is_zero && $values{"op${op}_loops"}->is_zero
            or fail("no-load receipt contains op $op activity");
    }
}
$values{loads} == Math::BigInt->new(1) or fail('expected exactly one provider load') if $require_load;
for my $expect (@require_ops) {
    my ($op, $min_events, $min_loops) = @$expect;
    $op_total{$op->numify} >= $min_events or fail("op $op event count below minimum");
    $values{"op${op}_status0"} >= $min_events or fail("op $op has too few successful events");
    $values{"op${op}_loops"} >= $min_loops or fail("op $op vector loop count below minimum");
}
for my $expect (@exact_ops) {
    my ($op, $events, $loops) = @$expect;
    $op_total{$op->numify}->bstr eq $events->bstr or fail("op $op event count mismatch");
    $values{"op${op}_status0"}->bstr eq $events->bstr or fail("op $op success count mismatch");
    $values{"op${op}_loops"}->bstr eq $loops->bstr or fail("op $op loop count mismatch");
}
for my $op (@success_only_ops) {
    $op_total{$op}->bstr eq $values{"op${op}_status0"}->bstr
        or fail("op $op contains a non-success event");
}
for my $op (@forbidden_ops) {
    $op_total{$op}->is_zero && $values{"op${op}_loops"}->is_zero
        or fail("unexpected activity for op $op");
}
exit 0;
