package BootstrapProductProducer;
use strict;
use warnings;
use Exporter 'import';
use Digest::SHA qw(sha256_hex);
our @EXPORT_OK = qw(read_product_producer validate_product_resources product_resource_profile validate_product_resource_profile);

sub validate_product_resources {
    my ($mode, $threads, $rss, $timeout, $rss_mode) = @_;
    $mode =~ /\A(?:qualified|diagnostic)\z/ && $rss_mode =~ /\A(?:enforce|monitor)\z/
        or die "invalid product policy mode\n";
    for my $number ($threads, $rss, $timeout) {
        defined($number) && $number =~ /\A(?:0|[1-9][0-9]*)\z/ or die "invalid product resource number\n";
    }
    $rss > 0 && $rss <= 6835937 or die "invalid product RSS observation limit\n";
    if ($mode eq 'qualified') {
        (($threads >= 10 && $threads <= 20) || $threads == 80) && $timeout > 0 && $rss_mode eq 'enforce'
            or die "qualified product policy differs\n";
    } else {
        $threads >= 1 && $threads <= 80 or die "diagnostic product workers exceed allocation\n";
    }
    return 1;
}

# Worker count is independent of frontend memory admission. Qualification still
# requires a finite deadline, enforced RSS, and the admitted producer proof.
sub product_resource_profile {
    validate_product_resources(@_);
    my ($mode, $threads) = @_;
    return 'diagnostic-v1' if $mode eq 'diagnostic';
    return $threads == 80 ? 'qualified-80-v1' : 'qualified-10-20-v1';
}

sub validate_product_resource_profile {
    my ($recorded, @resources) = @_;
    my $expected = product_resource_profile(@resources);
    # Old receipts are compatible only with the previously supported profiles.
    # New qualified80 evidence must explicitly bind every recorded layer.
    return $expected if !defined($recorded) && $expected ne 'qualified-80-v1';
    defined($recorded) && $recorded eq $expected
        or die "product resource profile differs\n";
    return $expected;
}

sub bytes {
    my ($path) = @_;
    -f $path && !-l $path && -s $path <= 262144 or die "producer proof unavailable: $path\n";
    open my $in, '<:raw', $path or die "producer proof unreadable\n";
    local $/; my $data = <$in>;
    close $in or die "producer proof close failed\n";
    return $data;
}
sub digest {
    my ($path) = @_;
    -f $path && !-l $path or die "producer input unavailable: $path\n";
    open my $in, '<:raw', $path or die "producer input unreadable\n";
    my $sha = Digest::SHA->new(256); $sha->addfile($in);
    close $in or die "producer input close failed\n";
    return $sha->hexdigest;
}
sub fields {
    my ($path) = @_;
    my $data = bytes($path);
    $data =~ /\n\z/ && $data !~ /[\r\0]/ or die "producer proof framing differs\n";
    my %field;
    for my $line (split /\n/, $data) {
        $line =~ /\A([a-z0-9_]+)=(.+)\z/ && !exists $field{$1}
            or die "producer proof field differs\n";
        $field{$1} = $2;
    }
    return %field;
}
sub equal {
    my ($field, $key, $expected) = @_;
    defined($field->{$key}) && $field->{$key} eq $expected or die "producer proof $key differs\n";
}
sub pin {
    my ($field, $path_key, $digest_key) = @_;
    defined($field->{$path_key}) && defined($field->{$digest_key}) &&
        $field->{$digest_key} =~ /\A[0-9a-f]{64}\z/ &&
        digest($field->{$path_key}) eq $field->{$digest_key}
        or die "producer proof $path_key changed\n";
}

sub read_product_producer {
    my ($path, $mode, $compiler, $compiler_sha, $source_root) = @_;
    $mode =~ /\A(?:qualified|diagnostic)\z/ or die "invalid producer qualification mode\n";
    my %proof = fields($path);
    equal(\%proof, 'candidate_path', $compiler);
    equal(\%proof, 'candidate_sha256', $compiler_sha);
    digest($compiler) eq $compiler_sha or die "producer bytes changed\n";
    if ($mode eq 'qualified') {
        equal(\%proof, 'schema', 'simple-bootstrap-stage2-admission-v2');
        equal(\%proof, 'status', 'admitted');
        return %proof;
    }
    equal(\%proof, 'schema', 'simple-subsystem-provisional-producer-v1');
    equal(\%proof, 'status', 'hello-qualified');
    equal(\%proof, 'diagnostic_only', '1');
    equal(\%proof, 'stage2_admitted', '0');
    equal(\%proof, 'dynload_provider', 'NOT_QUALIFIED');
    for my $pair ([qw(source_snapshot_path source_snapshot_sha256)],
        [qw(authority_path authority_sha256)], [qw(hello_receipt_path hello_receipt_sha256)],
        [qw(authority_verifier_path authority_verifier_sha256)],
        [qw(runtime_verifier_path runtime_verifier_sha256)]) { pin(\%proof, @$pair); }
    equal(\%proof, 'runtime_verifier_path', "$source_root/scripts/bootstrap/phase2-runtime-capsule.shs");
    for my $stage (qw(authority runtime)) {
        for my $kind (qw(stdout stderr exit)) { pin(\%proof, "${stage}_${kind}_path", "${stage}_${kind}_sha256"); }
        bytes($proof{"${stage}_exit_path"}) eq "0\n" or die "producer authority did not complete successfully\n";
    }
    my %authority = fields($proof{authority_path});
    equal(\%authority, 'schema', 'SIMPLE-PROVISIONAL-AUTHORITY-1');
    equal(\%authority, 'diagnostic_only', '1');
    equal(\%authority, 'producer_path', $compiler);
    equal(\%authority, 'producer_digest', $compiler_sha);
    equal(\%authority, 'source_snapshot_path', $proof{source_snapshot_path});
    equal(\%authority, 'source_snapshot_digest', $proof{source_snapshot_sha256});
    equal(\%authority, 'hello_receipt_path', $proof{hello_receipt_path});
    equal(\%authority, 'hello_receipt_digest', $proof{hello_receipt_sha256});
    my %hello = fields($proof{hello_receipt_path});
    equal(\%hello, 'producer_path', $compiler);
    equal(\%hello, 'producer_digest', $compiler_sha);
    equal(\%hello, 'compile_exit', '0'); equal(\%hello, 'run_exit', '0');
    for my $key (qw(hello_source hello_executable stdout stderr compile_command compile_log)) {
        pin(\%hello, "${key}_path", "${key}_digest");
    }
    my $capsule_path = ($proof{runtime_capsule_path} // '') . '/phase2-runtime-capsule.env';
    $proof{runtime_capsule_sha256} && digest($capsule_path) eq $proof{runtime_capsule_sha256}
        or die "producer runtime capsule changed\n";
    my %capsule = fields($capsule_path);
    equal(\%capsule, 'status', 'frozen');
    equal(\%capsule, 'compiler_sha256', $compiler_sha);
    equal(\%capsule, 'source_authority_path', $proof{runtime_authority_path});
    digest($proof{runtime_authority_path} . '/hosted-runtime.env') eq $capsule{hosted_authority_receipt_sha256}
        or die "producer runtime authority changed\n";
    return %proof;
}
1;
