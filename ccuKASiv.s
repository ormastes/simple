	.file	"runtime_time.c"
	.text
	.p2align 4
	.type	days_to_ymd, @function
days_to_ymd:
.LFB4:
	.cfi_startproc
	movq	%rcx, %r10
	movq	%rdi, %rcx
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsi, %r9
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	movq	%rdx, %r8
	addq	$719468, %rcx
	js	.L8
	movabsq	$4137408090565272301, %rax
	imulq	%rcx
	movq	%rcx, %rax
	sarq	$63, %rax
	sarq	$15, %rdx
	subq	%rax, %rdx
	movq	%rdx, %r11
.L3:
	imulq	$-146097, %r11, %rsi
	movabsq	$3234497591006606311, %rdi
	addq	%rcx, %rsi
	movq	%rsi, %rax
	movq	%rsi, %rbp
	imulq	%rdi
	sarq	$63, %rbp
	movabsq	$-1896998432287073591, %rax
	movq	%rbp, %rbx
	sarq	$8, %rdx
	subq	%rdx, %rbx
	imulq	%rsi
	addq	%rsi, %rbx
	leaq	(%rdx,%rsi), %rcx
	movq	%rcx, %rax
	sarq	$17, %rcx
	sarq	$15, %rax
	subq	%rbp, %rax
	subq	%rcx, %rbp
	addq	%rax, %rbx
	addq	%rbp, %rbx
	movq	%rbx, %rax
	imulq	%rdi
	movq	%rbx, %rdi
	leaq	(%r11,%r11,4), %rax
	sarq	$63, %rdi
	leaq	(%rax,%rax,4), %r11
	salq	$4, %r11
	movq	%rdx, %rcx
	sarq	$8, %rdx
	sarq	$6, %rcx
	subq	%rdi, %rdx
	subq	%rdi, %rcx
	leaq	(%rcx,%rcx,8), %rax
	addq	%rcx, %r11
	leaq	(%rcx,%rax,8), %rax
	leaq	(%rax,%rax,4), %rcx
	movabsq	$2070078458244228039, %rax
	addq	%rdx, %rcx
	imulq	%rbx
	movabsq	$3858142551364089227, %rax
	sarq	$12, %rdx
	subq	%rdx, %rdi
	addq	%rdi, %rcx
	subq	%rcx, %rsi
	leaq	(%rsi,%rsi,4), %rbx
	leaq	2(%rbx), %rcx
	imulq	%rcx
	movq	%rcx, %rax
	sarq	$63, %rax
	sarq	$5, %rdx
	movq	%rdx, %rcx
	subq	%rax, %rcx
	leaq	(%rcx,%rcx,8), %rax
	movq	%rax, %rdx
	salq	$4, %rdx
	leaq	2(%rax,%rdx), %rdi
	movabsq	$7378697629483820647, %rax
	imulq	%rdi
	sarq	$63, %rdi
	leaq	3(%rcx), %rax
	subq	$9, %rcx
	sarq	%rdx
	subq	%rdx, %rdi
	cmpq	$1527, %rbx
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 16
	popq	%rbp
	.cfi_def_cfa_offset 8
	cmovle	%rax, %rcx
	xorl	%eax, %eax
	leaq	1(%rsi,%rdi), %rdx
	cmpq	$2, %rcx
	setle	%al
	addq	%r11, %rax
	movl	%eax, (%r9)
	movl	%ecx, (%r8)
	movl	%edx, (%r10)
	ret
	.p2align 4,,10
	.p2align 3
.L8:
	.cfi_restore_state
	addq	$573372, %rdi
	movabsq	$4137408090565272301, %rax
	imulq	%rdi
	sarq	$63, %rdi
	sarq	$15, %rdx
	subq	%rdi, %rdx
	movq	%rdx, %r11
	jmp	.L3
	.cfi_endproc
.LFE4:
	.size	days_to_ymd, .-days_to_ymd
	.p2align 4
	.globl	rt_time_now_unix_micros
	.type	rt_time_now_unix_micros, @function
rt_time_now_unix_micros:
.LFB0:
	.cfi_startproc
	endbr64
	subq	$40, %rsp
	.cfi_def_cfa_offset 48
	xorl	%edi, %edi
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rsi
	call	clock_gettime@PLT
	movq	8(%rsp), %rcx
	movabsq	$2361183241434822607, %rax
	imulq	$1000000, (%rsp), %rsi
	imulq	%rcx
	sarq	$63, %rcx
	sarq	$7, %rdx
	subq	%rcx, %rdx
	leaq	(%rsi,%rdx), %rax
	movq	24(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L12
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L12:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE0:
	.size	rt_time_now_unix_micros, .-rt_time_now_unix_micros
	.p2align 4
	.globl	rt_time_now_nanos
	.type	rt_time_now_nanos, @function
rt_time_now_nanos:
.LFB1:
	.cfi_startproc
	endbr64
	subq	$40, %rsp
	.cfi_def_cfa_offset 48
	movq	%fs:40, %rax
	movq	%rax, 24(%rsp)
	xorl	%eax, %eax
	movl	initialized.1(%rip), %eax
	testl	%eax, %eax
	je	.L17
.L14:
	movq	%rsp, %rsi
	movl	$1, %edi
	call	clock_gettime@PLT
	movq	(%rsp), %rax
	subq	start.0(%rip), %rax
	movl	$0, %edx
	imulq	$1000000000, %rax, %rax
	addq	8(%rsp), %rax
	subq	8+start.0(%rip), %rax
	cmovs	%rdx, %rax
	movq	24(%rsp), %rdx
	subq	%fs:40, %rdx
	jne	.L18
	addq	$40, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
	.p2align 4,,10
	.p2align 3
.L17:
	.cfi_restore_state
	leaq	start.0(%rip), %rsi
	movl	$1, %edi
	call	clock_gettime@PLT
	movl	$1, initialized.1(%rip)
	jmp	.L14
.L18:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE1:
	.size	rt_time_now_nanos, .-rt_time_now_nanos
	.p2align 4
	.globl	rt_time_now_micros
	.type	rt_time_now_micros, @function
rt_time_now_micros:
.LFB2:
	.cfi_startproc
	endbr64
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	call	rt_time_now_nanos@PLT
	addq	$8, %rsp
	.cfi_def_cfa_offset 8
	movq	%rax, %rcx
	movabsq	$2361183241434822607, %rax
	imulq	%rcx
	sarq	$63, %r