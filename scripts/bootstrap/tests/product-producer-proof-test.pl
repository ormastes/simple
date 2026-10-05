#!/usr/bin/env perl
# Parser/binding tests only: fixture receipts do not claim native execution.
use strict;
use warnings;
use Test::More;
use File::Temp qw(tempdir);
use File::Path qw(make_path);
use Digest::SHA qw(sha256_hex);
use FindBin;
use lib "$FindBin::Bin/../lib";
use BootstrapProductProducer qw(read_product_producer);
my $root = tempdir(CLEANUP => 1);
make_path("$root/source/scripts/bootstrap", "$root/runtime", "$root/capsule");
sub write_bytes {
    my ($path, $bytes) = @_;
    open my $out, '>:raw', $path or die $!;
    print {$out} $bytes or die $!;
    close $out or die $!;
    return sha256_hex($bytes);
}
sub write_fields {
    my ($path, $fields) = @_;
    return write_bytes($path, join('', map { "$_=$fields->{$_}\n" } sort keys %$fields));
}
my %proof = (
    schema => 'simple-subsystem-provisional-producer-v1', status => 'hello-qualified',
    diagnostic_only => 1, stage2_admitted => 0, dynload_provider => 'NOT_QUALIFIED',
    candidate_path => "$root/compiler", candidate_sha256 => write_bytes("$root/compiler", 'compiler fixture'),
    source_snapshot_path => "$root/source.snapshot", source_snapshot_sha256 => write_bytes("$root/source.snapshot", 'snapshot fixture'),
    runtime_authority_path => "$root/runtime", runtime_capsule_path => "$root/capsule",
    authority_verifier_path => "$root/verifier", authority_verifier_sha256 => write_bytes("$root/verifier", 'verifier fixture'),
    runtime_verifier_path => "$root/source/scripts/bootstrap/phase2-runtime-capsule.shs",
    runtime_verifier_sha256 => write_bytes("$root/source/scripts/bootstrap/phase2-runtime-capsule.shs", 'runtime verifier fixture'),
    hello_receipt_path => "$root/hello.env", authority_path => "$root/authority.env",
);
my %hello = (format => 'SIMPLE-PROVISIONAL-HELLO-1', producer_path => $proof{candidate_path},
    producer_digest => $proof{candidate_sha256}, compile_exit => 0, run_exit => 0);
for my $key (qw(hello_source hello_executable stdout stderr compile_command compile_log)) {
    $hello{"${key}_path"} = "$root/hello.$key";
    $hello{"${key}_digest"} = write_bytes($hello{"${key}_path"}, "$key fixture");
}
$proof{hello_receipt_sha256} = write_fields($proof{hello_receipt_path}, \%hello);
my %authority = (schema => 'SIMPLE-PROVISIONAL-AUTHORITY-1', diagnostic_only => 1,
    producer_path => $proof{candidate_path}, producer_digest => $proof{candidate_sha256},
    source_snapshot_path => $proof{source_snapshot_path}, source_snapshot_digest => $proof{source_snapshot_sha256},
    hello_receipt_path => $proof{hello_receipt_path}, hello_receipt_digest => $proof{hello_receipt_sha256});
$proof{authority_sha256} = write_fields($proof{authority_path}, \%authority);
my %capsule = (schema => 'simple-phase2-runtime-capsule-v2', status => 'frozen',
    compiler_sha256 => $proof{candidate_sha256}, source_authority_path => $proof{runtime_authority_path},
    hosted_authority_receipt_sha256 => write_bytes("$root/runtime/hosted-runtime.env", 'runtime fixture'));
$proof{runtime_capsule_sha256} = write_fields("$root/capsule/phase2-runtime-capsule.env", \%capsule);
for my $stage (qw(authority runtime)) {
    for my $kind (qw(stdout stderr exit)) {
        my $key = "${stage}_${kind}";
        $proof{"${key}_path"} = "$root/$key";
        $proof{"${key}_sha256"} = write_bytes("$root/$key", $kind eq 'exit' ? "0\n" : "fixture $key\n");
    }
}
my $receipt = "$root/producer.env";
sub read_mode {
    my ($mode) = @_;
    return { read_product_producer($receipt, $mode, $proof{candidate_path}, $proof{candidate_sha256}, "$root/source") };
}
write_fields($receipt, \%proof);
is(read_mode('diagnostic')->{stage2_admitted}, 0, 'diagnostic remains unadmitted');
is(read_mode('diagnostic')->{dynload_provider}, 'NOT_QUALIFIED', 'no plugin-load inference');
ok(!eval { read_mode('qualified'); 1 }, 'diagnostic receipt cannot qualify formal product');
ok(!eval { read_mode('other'); 1 }, 'unknown qualification mode rejected');
for my $pair ([status => 'admitted'], [stage2_admitted => 1], [candidate_sha256 => 'a' x 64],
    [runtime_capsule_sha256 => 'b' x 64], [authority_sha256 => 'c' x 64],
    [hello_receipt_sha256 => 'd' x 64], [diagnostic_only => 0]) {
    my %changed = (%proof, $pair->[0] => $pair->[1]);
    write_fields($receipt, \%changed);
    ok(!eval { read_mode('diagnostic'); 1 }, "reject changed $pair->[0]");
}
write_fields($receipt, \%proof);
write_bytes($hello{stdout_path}, 'changed actual stdout');
ok(!eval { read_mode('diagnostic'); 1 }, 'actual Hello output change rejected');
write_bytes($hello{stdout_path}, 'stdout fixture');
my %crashed = %proof;
$crashed{authority_exit_sha256} = write_bytes($proof{authority_exit_path}, "139\n");
write_fields($receipt, \%crashed);
ok(!eval { read_mode('diagnostic'); 1 }, 'hashed raw verifier crash cannot become success');
write_bytes($proof{authority_exit_path}, "0\n");
my %other_authority = (%authority, producer_digest => 'e' x 64);
my %rebound = %proof;
$rebound{authority_sha256} = write_fields($proof{authority_path}, \%other_authority);
write_fields($receipt, \%rebound);
ok(!eval { read_mode('diagnostic'); 1 }, 'rehashed authority for another producer rejected');
write_fields($proof{authority_path}, \%authority);
write_fields($receipt, \%proof);
open my $extra, '>>:raw', $receipt or die $!; print {$extra} "status=hello-qualified\n"; close $extra;
ok(!eval { read_mode('diagnostic'); 1 }, 'duplicate proof key rejected');
my %formal = (schema => 'simple-bootstrap-stage2-admission-v2', status => 'admitted',
    candidate_path => $proof{candidate_path}, candidate_sha256 => $proof{candidate_sha256});
write_fields($receipt, \%formal);
is(read_mode('qualified')->{status}, 'admitted', 'formal producer schema remains separate');
ok(!eval { read_mode('diagnostic'); 1 }, 'formal receipt cannot silently select diagnostic policy');
done_testing();
