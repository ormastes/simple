#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use Errno qw(EEXIST ENOENT);
use Fcntl qw(
    O_RDONLY O_WRONLY O_CREAT O_EXCL O_NOFOLLOW O_DIRECTORY O_NONBLOCK
    F_GETFD F_SETFD FD_CLOEXEC S_ISREG S_IMODE
);
use File::Basename qw(dirname basename);

require 'syscall.ph';

my $force_cloexec_fallback =
    $ENV{SIMPLE_BOOTSTRAP_PRIVATE_PUBLISH_FORCE_CLOEXEC_FALLBACK} // q{};
my $O_CLOEXEC = $force_cloexec_fallback eq q{}
    ? (eval { Fcntl::O_CLOEXEC() } || 0)
    : 0;

sub ensure_cloexec {
    my ($fh, $label) = @_;
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) or die "get close-on-exec for $label: $!\n";
    if ($force_cloexec_fallback ne q{}) {
        defined(fcntl($fh, F_SETFD, $flags & ~FD_CLOEXEC))
            or die "force close-on-exec fallback for $label: $!\n";
        $flags = fcntl($fh, F_GETFD, 0);
        defined($flags) && ($flags & FD_CLOEXEC) == 0
            or die "verify forced close-on-exec fallback for $label: $!\n";
    }
    if (($flags & FD_CLOEXEC) == 0) {
        defined(fcntl($fh, F_SETFD, $flags | FD_CLOEXEC))
            or die "set close-on-exec for $label: $!\n";
    }
    my $verified = fcntl($fh, F_GETFD, 0);
    defined($verified) && ($verified & FD_CLOEXEC)
        or die "verify close-on-exec for $label: $!\n";
}

sub bind_fd {
    my ($fd, $label, $write_handle) = @_;
    my $fh;
    open($fh, $write_handle ? ">&=$fd" : "<&=$fd")
        or die "bind $label: $!\n";
    ensure_cloexec($fh, $label);
    return $fh;
}

sub openat_handle {
    my ($parent_fh, $leaf, $flags, $mode, $label) = @_;
    my $fd = syscall(&SYS_openat, fileno($parent_fh), $leaf,
        $flags | $O_CLOEXEC, $mode);
    $fd >= 0 or die "open $label: $!\n";
    return bind_fd($fd, $label);
}

my $sync_position = 0;
my $fail_sync_at =
    $ENV{SIMPLE_BOOTSTRAP_TEST_PRIVATE_PUBLISH_FAIL_SYNC_AT} // q{};
$fail_sync_at eq q{} || $fail_sync_at =~ /\A[1-9][0-9]*\z/
    or die "invalid private publication sync fault position\n";

sub sync_handle {
    my ($fh, $data_only, $label) = @_;
    ++$sync_position;
    if ($fail_sync_at ne q{} && $sync_position == $fail_sync_at) {
        die "injected sync failure at $sync_position ($label)\n";
    }
    my $operation = $data_only ? &SYS_fdatasync : &SYS_fsync;
    syscall($operation, fileno($fh)) == 0 or die "sync $label: $!\n";
}

sub safe_relative_parts {
    my ($relative) = @_;
    $relative =~ /\A[A-Za-z0-9._\/-]+\z/ &&
        $relative !~ /\A\// && $relative !~ /\A\.\.?\z/ &&
        $relative !~ m{(?:\A|/)\.\.?(?:/|\z)} &&
        $relative !~ m{//}
        or die "unsafe tuple member\n";
    return split m{/}, $relative;
}

sub sync_tuple_member {
    my ($staging_fh, $relative) = @_;
    my @parts = safe_relative_parts($relative);
    my $leaf = pop @parts;
    my $parent_fh = $staging_fh;
    my @directory_fhs;
    for my $part (@parts) {
        my $next = openat_handle($parent_fh, $part,
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW, 0,
            "tuple directory $part");
        push @directory_fhs, $next;
        $parent_fh = $next;
    }
    my $file_fh = openat_handle($parent_fh, $leaf,
        O_RDONLY | O_NOFOLLOW | O_NONBLOCK, 0,
        "tuple member $relative");
    my @file_stat = stat($file_fh);
    @file_stat && S_ISREG($file_stat[2])
        or die "tuple member is not regular: $relative\n";
    my $sha = Digest::SHA->new(256);
    $sha->addfile($file_fh, "b")
        or die "hash tuple member $relative\n";
    sync_handle($file_fh, 1, "tuple member $relative");
    my @file_after = stat($file_fh);
    @file_after && $file_stat[0] == $file_after[0] &&
        $file_stat[1] == $file_after[1] &&
        $file_stat[2] == $file_after[2] &&
        $file_stat[7] == $file_after[7] &&
        $file_stat[9] == $file_after[9] &&
        $file_stat[10] == $file_after[10]
        or die "tuple member changed while hashing: $relative\n";
    for my $directory_fh (reverse @directory_fhs) {
        sync_handle($directory_fh, 0, "tuple directory for $relative");
    }
    my $digest = $sha->hexdigest;
    return {
        digest => $digest,
        record => join(":", "file-hex", unpack("H*", $relative),
            (($file_stat[2] & 0111) ? 1 : 0), $digest),
    };
}

sub same_identity {
    my ($left, $right) = @_;
    return @$left && @$right &&
        $left->[0] == $right->[0] && $left->[1] == $right->[1];
}

sub quarantine_leaf {
    my ($parent_fh, $leaf, $observed_identity) = @_;
    my $RENAME_NOREPLACE = 1;
    for my $attempt (0 .. 1023) {
        my $quarantine = "$leaf.rejected.$$.$attempt";
        if (syscall(&SYS_renameat2, fileno($parent_fh), $leaf,
                fileno($parent_fh), $quarantine, $RENAME_NOREPLACE) == 0) {
            my $quarantine_fh = openat_handle($parent_fh, $quarantine,
                O_RDONLY | O_DIRECTORY | O_NOFOLLOW, 0,
                "quarantined private authority");
            my @quarantined = stat($quarantine_fh);
            same_identity($observed_identity, \@quarantined)
                or die "quarantined private authority identity changed\n";
            sync_handle($parent_fh, 0, "generation parent after quarantine");
            return $quarantine;
        }
        next if $! == EEXIST;
        die "quarantine rejected private authority: $!\n";
    }
    die "quarantine rejected private authority: name space exhausted\n";
}

@ARGV >= 6 or die
    "usage: $0 STAGING FINAL RECEIPT INPUTS_FINGERPRINT " .
    "PREPARED_HASH TUPLE_MEMBER...\n";
my ($staging, $final, $receipt, $fingerprint, $prepared_hash,
    @tuple_members) = @ARGV;
$fingerprint =~ /\A[0-9a-f]{64}\z/ or die "invalid inputs fingerprint\n";
$prepared_hash =~ /\A[0-9a-f]{64}\z/ or die "invalid prepared tuple hash\n";
dirname($staging) eq dirname($final) or die "staging/final parents differ\n";
dirname($receipt) eq $final or die "receipt must publish inside final authority\n";
basename($final) eq "$fingerprint-$prepared_hash"
    or die "final authority name does not bind prepared tuple hash\n";
for my $leaf (basename($staging), basename($final), basename($receipt)) {
    $leaf =~ /\A[A-Za-z0-9._-]+\z/ && $leaf ne q{.} && $leaf ne q{..}
        or die "unsafe publication leaf\n";
}
my %seen;
for my $member (@tuple_members) {
    safe_relative_parts($member);
    !$seen{$member}++ or die "duplicate tuple member\n";
    $member ne basename($receipt) or die "receipt listed as tuple member\n";
}

my $directory_flags = O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC;
sysopen(my $generation_parent, dirname($final), $directory_flags)
    or die "open generation parent: $!\n";
ensure_cloexec($generation_parent, "generation parent");
my @generation_parent_before = stat($generation_parent);
@generation_parent_before or die "stat generation parent: $!\n";
my $generation_parent_original_mode = S_IMODE($generation_parent_before[2]);

# Bind the staging leaf through the generation parent. Every later lookup,
# including the rename and committed-final check, stays relative to this same
# parent descriptor.
my $staging_fh = openat_handle($generation_parent, basename($staging),
    O_RDONLY | O_DIRECTORY | O_NOFOLLOW, 0, "staging directory");
my @staging_before = stat($staging_fh);
@staging_before or die "stat staging directory: $!\n";
my $staging_original_mode = S_IMODE($staging_before[2]);

# An already-present final is rejected before the staging directory is thawed
# or a receipt is created. Non-ENOENT lookup failures are also collisions.
my $existing_fd = syscall(&SYS_openat, fileno($generation_parent),
    basename($final), O_RDONLY | O_NOFOLLOW | O_NONBLOCK | $O_CLOEXEC, 0);
if ($existing_fd >= 0) {
    my $existing_fh = bind_fd($existing_fd, "existing final");
    close($existing_fh) or die "close existing final: $!\n";
    die "private authority collision/commit failure: final exists\n";
}
$! == ENOENT or die "private authority collision/commit failure: $!\n";

# Flush every consumer tuple member and its nested directory entries before
# any receipt or namespace commit can make the generation admissible.
my @tuple_snapshot_records;
my %tuple_digest;
for my $member (@tuple_members) {
    my $observation = sync_tuple_member($staging_fh, $member);
    push @tuple_snapshot_records, $observation->{record};
    $tuple_digest{$member} = $observation->{digest};
}
my $observed_prepared_hash = sha256_hex(
    join("\n", sort @tuple_snapshot_records) . "\n");
$observed_prepared_hash eq $prepared_hash
    or die "prepared tuple hash changed before private publication\n";

@tuple_members == 5 or die "private tuple member count mismatch\n";
my ($seed_name, $native_name, $backfill_name, $stamp_name, $runtime_name) =
    @tuple_members;
$stamp_name eq "$seed_name.inputs.sha256" && $stamp_name !~ m{/}
    or die "private tuple stamp name mismatch\n";
my $expected_runtime_name = $native_name eq "libsimple_native_all.a"
    ? "deps/libsimple_runtime.a"
    : $native_name eq "simple_native_all.lib"
        ? "deps/simple_runtime.lib" : q{};
$expected_runtime_name ne q{} && $runtime_name eq $expected_runtime_name
    or die "private tuple runtime name mismatch\n";
my $stamp_fh = openat_handle($staging_fh, $stamp_name,
    O_RDONLY | O_NOFOLLOW | O_NONBLOCK, 0, "private tuple stamp");
my $stamp_body = q{};
while (1) {
    my $chunk = q{};
    my $read = sysread($stamp_fh, $chunk, 4096);
    defined($read) or die "read private tuple stamp: $!\n";
    last if $read == 0;
    $stamp_body .= $chunk;
    length($stamp_body) <= 8192 or die "private tuple stamp too large\n";
}
sha256_hex($stamp_body) eq $tuple_digest{$stamp_name}
    or die "private tuple stamp changed after durable hash\n";
my $expected_stamp =
    "schema=simple-bootstrap-seed-artifact-stamp-v2\n" .
    "inputs_fingerprint=$fingerprint\n" .
    "seed_sha256=$tuple_digest{$seed_name}\n" .
    "native_all_sha256=$tuple_digest{$native_name}\n" .
    "backfill_status=present\n" .
    "backfill_sha256=$tuple_digest{$backfill_name}\n";
$stamp_body eq $expected_stamp
    or die "private tuple stamp contents do not bind prepared artifacts\n";
sync_handle($staging_fh, 0, "staged tuple directory");

my $receipt_fh;
my $receipt_created = 0;
my $publication_error;
my $final_present = 0;
my @final_identity;
my $generation_parent_sealed = 0;
{
    local $@;
    eval {
        # Preparation freezes the tuple at 0500. Thaw only this already-bound
        # descriptor, then restore the original mode on every pre-commit error.
        syscall(&SYS_fchmod, fileno($staging_fh), 0700) == 0
            or die "thaw staged authority for receipt: $!\n";

        my $receipt_fd = syscall(&SYS_openat, fileno($staging_fh),
            basename($receipt),
            O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | $O_CLOEXEC, 0400);
        $receipt_fd >= 0
            or die "private publication receipt collision: $!\n";
        $receipt_created = 1;
        $receipt_fh = bind_fd($receipt_fd, "private publication receipt", 1);
        syscall(&SYS_fchmod, fileno($receipt_fh), 0400) == 0
            or die "set receipt mode: $!\n";
        my $body = "schema=simple-bootstrap-rust-publication-v1\n" .
            "global_publication_status=not-requested\n" .
            "inputs_fingerprint=$fingerprint\n" .
            "prepared_tuple_hash=$prepared_hash\n" .
            "private_authority=$final\n";
        while (length $body) {
            my $written = syswrite($receipt_fh, $body);
            defined($written) && $written > 0 or die "write receipt: $!\n";
            substr($body, 0, $written, q{});
        }
        sync_handle($receipt_fh, 1, "publication receipt");
        close($receipt_fh) or die "close receipt: $!\n";
        undef $receipt_fh;
        sync_handle($staging_fh, 0, "receipt directory");
        syscall(&SYS_fchmod, fileno($staging_fh), 0500) == 0
            or die "freeze staged authority: $!\n";
        sync_handle($staging_fh, 0, "staged authority");

        # Rebind the source leaf at the commit boundary. A replacement leaf
        # cannot be accepted merely because the original descriptor survived.
        my $staging_leaf_fh = openat_handle($generation_parent,
            basename($staging), O_RDONLY | O_DIRECTORY | O_NOFOLLOW, 0,
            "staging leaf at commit");
        my @staging_leaf_stat = stat($staging_leaf_fh);
        same_identity(\@staging_before, \@staging_leaf_stat)
            or die "staging authority identity changed before commit\n";

        my $RENAME_NOREPLACE = 1;
        syscall(&SYS_renameat2, fileno($generation_parent), basename($staging),
            fileno($generation_parent), basename($final),
            $RENAME_NOREPLACE) == 0
            or die "private authority collision/commit failure: $!\n";
        $final_present = 1;

        # The final namespace leaf, not just the still-open source descriptor,
        # must resolve to the exact device/inode that was prepared and synced.
        my $final_fh = openat_handle($generation_parent, basename($final),
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW, 0,
            "committed final authority");
        my @committed_final = stat($final_fh);
        @final_identity = @committed_final;
        if (!same_identity(\@staging_before, \@committed_final)) {
            my $quarantine = quarantine_leaf($generation_parent,
                basename($final), \@committed_final);
            $final_present = 0;
            die "committed final authority identity changed; " .
                "rejected leaf quarantined as $quarantine\n";
        }
        sync_handle($generation_parent, 0, "generation parent");

        # Close the last pathname-only success window.  Once the parent is
        # non-writable, rebind the final leaf and require the prepared identity
        # again.  Admission may safely reopen this sealed namespace after the
        # publisher exits; a substitute observed before sealing is quarantined.
        syscall(&SYS_fchmod, fileno($generation_parent), 0500) == 0
            or die "seal generation parent: $!\n";
        $generation_parent_sealed = 1;
        sync_handle($generation_parent, 0, "sealed generation parent");
        my $sealed_final_fh = openat_handle($generation_parent,
            basename($final), O_RDONLY | O_DIRECTORY | O_NOFOLLOW, 0,
            "sealed final authority");
        my @sealed_final = stat($sealed_final_fh);
        if (!same_identity(\@staging_before, \@sealed_final)) {
            syscall(&SYS_fchmod, fileno($generation_parent),
                $generation_parent_original_mode) == 0
                or die "thaw generation parent after final substitution: $!\n";
            $generation_parent_sealed = 0;
            my $quarantine = quarantine_leaf($generation_parent,
                basename($final), \@sealed_final);
            $final_present = 0;
            die "sealed final authority identity changed; " .
                "rejected leaf quarantined as $quarantine\n";
        }
        @final_identity = @sealed_final;
        1;
    } or $publication_error = $@ || "private publication failed\n";
}

if (defined $publication_error) {
    close($receipt_fh) if defined($receipt_fh);
    my @rollback_errors;
    if ($generation_parent_sealed) {
        if (syscall(&SYS_fchmod, fileno($generation_parent),
                $generation_parent_original_mode) == 0) {
            $generation_parent_sealed = 0;
        } else {
            push @rollback_errors, "thaw generation parent rollback: $!";
        }
    }
    if ($final_present) {
        eval {
            quarantine_leaf($generation_parent, basename($final),
                \@final_identity);
            $final_present = 0;
            1;
        } or push @rollback_errors,
            "quarantine post-rename failure: " . ($@ || "unknown failure");
    }
    if ($receipt_created) {
        syscall(&SYS_fchmod, fileno($staging_fh), 0700) == 0
            or push @rollback_errors, "thaw rollback: $!";
        syscall(&SYS_unlinkat, fileno($staging_fh), basename($receipt), 0) == 0
            or push @rollback_errors, "remove rollback receipt: $!";
    }
    syscall(&SYS_fchmod, fileno($staging_fh), $staging_original_mode) == 0
        or push @rollback_errors, "restore staging mode: $!";
    eval { sync_handle($staging_fh, 0, "staging rollback"); 1; }
        or push @rollback_errors,
            "sync staging rollback: " . ($@ || "unknown failure");
    if (@rollback_errors) {
        $publication_error .= "rollback failure: " .
            join(q{; }, @rollback_errors) . "\n";
    }
    die $publication_error;
}

exit 0;
