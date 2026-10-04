; SPDX-License-Identifier: MIT OR Apache-2.0 OR GPL-2.0-only OR GPL-3.0-only
; Copyright (c) 2025 Ben8282 and the-math-thingy contributors
; ===========================================================================
; goldbach.asm — Goldbach conjecture verifier, x86-64 Linux, no libc.
;
;   Build:  Linux:   bash build.sh      (nasm -felf64 + ld)
;           Windows: build.cmd          (nasm -fwin64 -DWIN64 + ld or lld-link;
;                                        no C runtime, no import libraries)
;   Runs on any x86-64 CPU; AVX2 and POPCNT are used when present.
;   Run:    ./goldbach [--threads N] [--start N] [--until N] [--log] [--check]
;   Commands while running: status | stop | quit     (Ctrl-C = stop)
;
; HOW IT WORKS
;   Even numbers are processed in chunks of CHUNK = 133,693,440 numbers.  Each
;   chunk is R = 32 segments; a segment is a bitmap of W = 2^21 odd numbers
;   (256 KB, fits L2).  Per segment:
;     1. Segmented sieve of Eratosthenes marks composite odd numbers using a
;        base prime table that starts at 2^26 and doubles whenever a chunk
;        needs more (up to 2^32 = sqrt(2^64)), so every 64-bit N is covered.
;        The only limit is the 64-bit integer range itself (N <= 2^64 - 2).
;     2. Word-parallel Goldbach pass: for the k-th odd prime p the set of
;        even N with N-p prime is just the prime bitmap shifted by (PMAX-p)/2
;        bits, so 256 even numbers are resolved per AVX2 instruction.  The
;        pass for prime p runs while unresolved N remain; the last pass that
;        resolves anything gives the segment's "most difficult number".
;     3. Once few N remain, each is finished individually (sparse phase).
;     4. N still unresolved after all primes <= PMAX go to an exhaustive
;        search with deterministic Miller-Rabin (never expected to happen:
;        the largest minimal p known for N <= 4e18 is 9781 < PMAX).
;   Worker threads claim chunks with an atomic counter; a ring of completion
;   slots lets results be merged strictly in order of N, so records and the
;   checkpoint are deterministic.  Checkpoints are written atomically
;   (tmp + rename) and read back on startup to resume.
;
; "Checks" convention (kept from the original program): a partition with
;   prime p counts as pi(p) checks, i.e. 2 -> 1, 3 -> 2, 5 -> 3, ...
; ===========================================================================

bits 64
default rel                              ; position-independent: required for Windows PE, fine for ELF

%ifndef WIN64
; ---- Linux syscalls -------------------------------------------------------
%define SYS_read                0
%define SYS_write               1
%define SYS_open                2
%define SYS_close               3
%define SYS_mmap                9
%define SYS_rt_sigaction       13
%define SYS_rt_sigprocmask     14
%define SYS_rt_sigreturn       15
%define SYS_nanosleep          35
%define SYS_getpid             39
%define SYS_clone              56
%define SYS_exit               60
%define SYS_kill               62
%define SYS_rename             82
%define SYS_futex             202
%define SYS_sched_getaffinity 204
%define SYS_clock_gettime     228
%define SYS_exit_group        231

%define O_RDONLY   0
%define O_WRONLY   1
%define O_CREAT    0x40
%define O_TRUNC    0x200
%define O_APPEND   0x400
%define PROT_RW    3
%define MAP_PRIV_ANON 0x4022     ; MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE (pages appear when touched)
%define CLONE_FLAGS 0x350F00     ; VM|FS|FILES|SIGHAND|THREAD|SYSVSEM|PARENT_SETTID|CHILD_CLEARTID
%define FUTEX_WAIT 0
%define SA_RESTORER 0x04000000
%define SIGINT  2
%define SIGUSR1 10
%define SIGTERM 15
%define EINTR   4
%endif

; ---- tuning constants -----------------------------------------------------
W             equ 1 << 21              ; odd-number slots per segment
WQ            equ W / 64               ; qwords in a segment bitmap
WPAD          equ 8                    ; padding qwords after the bitmap
HALFP         equ 8192                 ; overlap between segments (bits)
PMAX          equ 2*HALFP + 1          ; fast-path primes are the odd primes <= PMAX
E             equ W - HALFP            ; even numbers verified per segment
EQ            equ E / 64               ; qwords in the unresolved bitmap (multiple of 4)
R             equ 32                   ; segments per chunk
CHUNK            equ R * 2 * E            ; numbers per chunk
BASE_INIT     equ 1 << 26              ; base primes sieved at startup; the table doubles as N grows
BASE_BITS     equ BASE_INIT / 2
BASE_MAX      equ 1 << 32              ; final size = sqrt(2^64): every prime a 64-bit N can need
BASE_BYTES_MAX equ BASE_MAX / 16       ; odd-number bitmap up to BASE_MAX (256 MB, reserved lazily)
MAX_BASE      equ 1 << 28              ; prime list capacity (pi(2^32) = 203,280,221)
MAX_FAST      equ 2048
RING          equ 256                  ; completion ring (power of two)
SMALL_END     equ 1 << 20              ; N below this use the simple scalar path
SPARSE_THRESH equ E / 128
CP_SECS       equ 2                    ; seconds between checkpoint writes
MAX_THREADS   equ 256
SEG_LAST_OFF  equ 2*(R-1)*E + 2*W - 2  ; offset of the last sieved odd number in a chunk

; ---- per-thread context layout (one mmap per worker), derived from W -------
CTX_COMP      equ 0                    ; composite bitmap, (WQ+WPAD) qwords
CTX_HDR       equ (((WQ+WPAD)*8 + 0xFFF) & ~0xFFF)
CTX_UNRES     equ CTX_HDR + 0x1000     ; unresolved bitmap, EQ qwords + pad (32-byte aligned)
CTX_NEXTJ     equ CTX_UNRES + (((EQ+8)*8 + 0xFFF) & ~0xFFF)   ; uint32 next index per base prime (1 GB virtual, touched as needed)
CTX_LOGBUF    equ CTX_NEXTJ + MAX_BASE*4
LOGBUF_SIZE   equ 65536
CTX_FIRSTN    equ CTX_LOGBUF + LOGBUF_SIZE   ; u64[MAX_FAST+2]: first N of each depth in the segment
FIRSTN_SIZE   equ 0x5000
CTX_STACK     equ CTX_FIRSTN + FIRSTN_SIZE
STACK_SIZE    equ 262144
CTX_SIZE      equ CTX_STACK + STACK_SIZE

HDR_TID       equ CTX_HDR + 0          ; thread id, cleared by the kernel on exit
HDR_IDX       equ CTX_HDR + 8
HDR_MAXD      equ CTX_HDR + 16         ; chunk: running maximum fast-path depth
HDR_FBC       equ CTX_HDR + 32         ; chunk: fallback activations
HDR_FBD       equ CTX_HDR + 40         ; chunk: running maximum fallback depth
HDR_VIO       equ CTX_HDR + 56         ; chunk: violations
HDR_PC        equ CTX_HDR + 64         ; chunk: primes counted
HDR_NUSE      equ CTX_HDR + 72         ; base primes needed for this chunk
HDR_SEGBASE   equ CTX_HDR + 80         ; first odd number of the current segment
HDR_SEGMAXD   equ CTX_HDR + 88         ; segment: deepest depth / first N (for --check)
HDR_SEGMAXN   equ CTX_HDR + 96
HDR_CHKD      equ CTX_HDR + 104        ; --check: vector result kept for comparison
HDR_CHKN      equ CTX_HDR + 112
HDR_LOGSB     equ CTX_HDR + 128        ; string builder {ptr, len, cap} for --log
HDR_SLOT      equ CTX_HDR + 152        ; ring slot of the chunk being processed
HDR_NREC      equ CTX_HDR + 160        ; records appended to that slot
HDR_NFB       equ CTX_HDR + 168
HDR_JBIAS     equ CTX_HDR + 176        ; 0 in a chunk's first segment, HALFP afterwards (see sieve_segment)
HDR_COMMITTED equ CTX_HDR + 184        ; bytes of next_j made usable so far (Windows commits lazily)

; ring slot: statistics of one chunk plus its record candidates, i.e. the
; running maxima of the depth in order of N within the chunk.
SLOT_SIZE     equ 8192
SLOT_DONE     equ 0                    ; chunk index + 1 when complete
SLOT_FBC      equ 8
SLOT_VIO      equ 16
SLOT_PC       equ 24
SLOT_NREC     equ 32
SLOT_NFB      equ 40
SLOT_RECS     equ 64                   ; (N, depth) pairs, fast path
SLOT_FBRECS   equ 4096                 ; (N, depth) pairs, fallback
MAXREC        equ 248
MAXFBREC      equ 256

; ===========================================================================
section .rodata
; ===========================================================================
mask8:          db 1,2,4,8,16,32,64,128
mr_witnesses:   db 2,3,5,7,11,13,17,19,23,29,31,37

s_banner:       db "Is every even integer > 2 the sum of two primes?  (x86-64 assembly edition)",10,0
s_using:        db "Using ",0
s_workers:      db " worker thread(s).  Commands: status | stop | quit   (Ctrl-C = stop)",10,0
s_building:     db "Building base prime table (primes up to ",0
s_builddone:    db ") ... done: ",0
s_primes_nl:    db " primes; the table grows automatically as N increases.",10,0
s_resume:       db "Resuming from checkpoint: verified up to ",0
s_fresh:        db "Starting from ",0
s_nl:           db 10,0
s_running:      db "Running.",10,0
s_prompt:       db "> ",0
s_cmds:         db "Commands: status | stop | quit",10,0
s_forcequit:    db "Force quitting.",10,0
s_stopping:     db "Stopping (finishing chunks in flight)...",10,0
s_sum1:         db "[Goldbach] Verified up to ",0
s_sum2:         db ". Violations: ",0
s_sum3:         db ".",10,0
s_limit:        db "[Goldbach] Reached the end of the 64-bit integer range: nothing larger can be represented.",10,0
s_cpu_avx2:     db "CPU paths: AVX2",0
s_cpu_plain:    db "CPU paths: plain x86-64 (no AVX2)",0
s_cpu_popcnt:   db " + POPCNT",0
s_cp_err:       db "ERROR: cannot create checkpoint.tmp",10,0
s_open_err:     db "ERROR: cannot open output file: ",0
s_check_fail:   db "SELF-CHECK MISMATCH at segment base ",0
s_check_v:      db "  vector: depth ",0
s_check_s:      db "  scalar: depth ",0
s_check_n:      db " at N=",0
s_badarg:       db "Unknown option: ",0
s_usage:        db "Usage: goldbach [--threads N] [--start N] [--until N] [--log] [--check] [--nfast K] [--baseline]",10,0

s_st_ver:       db "Goldbach verified       : up to ",0
s_st_pi:        db "Primes up to that bound : ",0
s_st_rate:      db "Rate since start        : ",0
s_st_rate2:     db " numbers/s",10,0
s_st_fa:        db "Fallback activations    : ",0
s_st_lfn:       db "Largest fallback N      : ",0
s_st_mfd:       db "Deepest fallback depth  : ",0
s_st_mfsd:      db "Largest fast-path depth : ",0
s_st_mfsn:      db "Largest fast-path N     : ",0
s_st_vio:       db "Violations found        : ",0
s_st_none:      db "No violations found so far.",10,0

s_rec_fast:     db "NEW MOST DIFFICULT NUMBER FOUND",10,10,0
s_rec_fb:       db "NEW EMERGENCY SEARCH RECORD",10,10,0
s_rec_num:      db "Number=",0
s_rec_chk:      db 10,10,"Checks needed before finding a Goldbach pair=",0
s_rec_ts:       db 10,10,"Timestamp=",0
s_rec_end:      db 10,10,0
s_vio1:         db "VIOLATION: ",0
s_vio2:         db " has no prime pair!",10,0
s_vio_out1:     db 10,"*** VIOLATION: ",0
s_vio_out2:     db " has no prime pair! ***",10,"> ",0
s_eq:           db " = ",0
s_plus:         db " + ",0
s_utc:          db " UTC",0

f_checkpoint:   db "checkpoint.txt",0
f_cp_tmp:       db "checkpoint.tmp",0
f_interesting:  db "interesting_cases.txt",0
f_violations:   db "violations.txt",0
f_log:          db "goldbach.txt",0

; checkpoint lines: key text, then the global it loads into / is written from
k_ver:          db "Goldbach verified up to: ",0
k_fail:         db "Goldbach failures found: ",0
k_fbc:          db "Times the emergency search was needed: ",0
k_fbn:          db "Largest number that needed the emergency search: ",0
k_fbd:          db "Most work ever needed during an emergency search: ",0
k_maxn:         db "Number that was most difficult to verify: ",0
k_maxd:         db "Most difficult number checked so far: ",0
k_pc:           db "Primes counted up to the verified bound: ",0
k_ts:           db "Timestamp: ",0
s_checks:       db " checks",0

o_threads:      db "--threads",0
o_start:        db "--start",0
o_until:        db "--until",0
o_log:          db "--log",0
o_check:        db "--check",0
o_nfast:        db "--nfast",0
o_help:         db "--help",0
o_baseline:     db "--baseline",0
c_status:       db "status",0
c_stop:         db "stop",0
c_quit:         db "quit",0

align 8
cp_table:       dq k_ver,  g_cp_verified
                dq k_fail, g_violations
                dq k_fbc,  g_fb_count
                dq k_fbn,  g_fb_max_N
                dq k_fbd,  g_fb_max_depth
                dq k_maxn, g_max_N
                dq k_maxd, g_max_depth
                dq k_pc,   g_prime_count
                dq 0, 0

; ===========================================================================
section .bss
; ===========================================================================
align 64
g_slots:        resb RING * SLOT_SIZE
g_shift:        resd MAX_FAST               ; (PMAX - p_k) / 2 for the k-th odd prime
g_ctx:          resq MAX_THREADS

g_base_bits:    resq 1
g_base_primes:  resq 1
g_n_base:       resq 1
g_base_limit:   resq 1                      ; odd numbers below this are sieved in g_base_bits
g_grow_lock:    resq 1
g_n_fast:       resq 1
g_nfast_opt:    resq 1

g_N0:           resq 1                      ; first even number of chunk 0
g_run_start:    resq 1                      ; g_verified when the workers started
g_cp_verified:  resq 1
g_next_chunk:   resq 1
g_frontier:     resq 1
g_verified:     resq 1
g_active:       resq 1
g_lock:         resq 1
g_vlock:        resq 1
g_stop:         resq 1
g_end64:        resq 1                      ; set when the next chunk would pass 2^64
g_until:        resq 1
g_nthreads:     resq 1
g_log_mode:     resq 1
g_check_mode:   resq 1
g_start_opt:    resq 1
g_fd_int:       resq 1
g_fd_vio:       resq 1
g_fd_log:       resq 1
g_vec_pass:     resq 1                      ; vec_pass_avx2 or vec_pass_scalar
g_have_avx2:    resb 1
g_have_popcnt:  resb 1
g_t0_ms:        resq 1
g_last_cp_ms:   resq 1

g_max_depth:    resq 1
g_max_N:        resq 1
g_fb_count:     resq 1
g_fb_max_depth: resq 1
g_fb_max_N:     resq 1
g_violations:   resq 1
g_prime_count:  resq 1

; string builders {ptr, len, cap}
g_outsb:        resq 3                      ; main thread
g_msb:          resq 3                      ; merge / records / checkpoint (under g_lock)
g_vsb:          resq 3                      ; violations (under g_vlock)
g_logsb:        resq 3                      ; --log on the main thread (small path)
g_outbuf:       resb 4096
g_mbuf:         resb 4096
g_vbuf:         resb 512
g_logbuf:       resb LOGBUF_SIZE
g_cpbuf:        resb 2048
g_linebuf:      resb 256
g_cmdbuf:       resb 64
g_tspec:        resq 2
g_sigact:       resq 4
g_sigset:       resq 1
g_cpumask:      resb 128
g_hstdin:       resq 1                      ; OS handles for the console (0/1 on Linux)
g_hstdout:      resq 1
g_main_thread:  resq 1                      ; Windows: real handle of the main thread
g_cmdline:      resb 4096                   ; Windows: copy of the command line
g_argblock:     resq 64                     ; Windows: argc followed by argv pointers

; ===========================================================================
section .text
global _start
; ===========================================================================

; ---------------------------------------------------------------------------
; Small helpers.  Internal convention: args rdi, rsi, rdx, rcx, r8, r9;
; return rax (rdx); rbx, rbp, r12-r15 preserved.  Worker-side code keeps
; r15 = its context pointer at all times.
; ---------------------------------------------------------------------------

; write_all(rdi=handle, rsi=buf, rdx=len): write everything (OS layer below)
write_all:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, rsi
    mov r13, rdx
.loop:
    test r13, r13
    jz .done
    mov rdi, rbx
    mov rsi, r12
    mov rdx, r13
    call os_write
    test rax, rax
    jle .done
    add r12, rax
    sub r13, rax
    jmp .loop
.done:
    pop r13
    pop r12
    pop rbx
    ret

; sb_init(rdi=sb, rsi=buffer, rdx=cap)
sb_init:
    mov [rdi], rsi
    mov qword [rdi+8], 0
    mov [rdi+16], rdx
    ret

; sb_putc(rdi=sb, esi=char)
sb_putc:
    mov rax, [rdi+8]
    cmp rax, [rdi+16]
    jae .full
    mov rcx, [rdi]
    mov [rcx+rax], sil
    inc qword [rdi+8]
.full:
    ret

; sb_puts(rdi=sb, rsi=ptr, rdx=len)
sb_puts:
    mov rax, [rdi+8]
    mov rcx, [rdi+16]
    sub rcx, rax
    cmp rdx, rcx
    cmova rdx, rcx
    mov r8, [rdi]
    add r8, rax
    add [rdi+8], rdx
    push rdi
    mov rdi, r8
    mov rcx, rdx
    rep movsb
    pop rdi
    ret

; sb_putz(rdi=sb, rsi=NUL-terminated string)
sb_putz:
    mov rdx, -1
.len:
    inc rdx
    cmp byte [rsi+rdx], 0
    jne .len
    jmp sb_puts

; sb_putu(rdi=sb, rsi=value): unsigned decimal
sb_putu:
    sub rsp, 32
    lea r8, [rsp+32]
    mov rax, rsi
    mov r9d, 10
    xor ecx, ecx
.digit:
    xor edx, edx
    div r9
    add dl, '0'
    dec r8
    mov [r8], dl
    inc rcx
    test rax, rax
    jnz .digit
    mov rsi, r8
    mov rdx, rcx
    call sb_puts
    add rsp, 32
    ret

; sb_put2(rdi=sb, esi=value): two-digit zero-padded (value < 100)
sb_put2:
    push rdi
    push rsi
    cmp esi, 10
    jae .two
    mov esi, '0'
    call sb_putc
.two:
    pop rsi
    pop rdi
    jmp sb_putu

; sb_flush(rdi=sb, rsi=handle): write the buffer and empty it
sb_flush:
    push rbx
    mov rbx, rdi
    mov rdi, rsi
    mov rsi, [rbx]
    mov rdx, [rbx+8]
    call write_all
    mov qword [rbx+8], 0
    pop rbx
    ret

; puts_out(rdi=zstr): write a string to stdout immediately
puts_out:
    push rbx
    mov rbx, rdi
    mov rdx, -1
.len:
    inc rdx
    cmp byte [rbx+rdx], 0
    jne .len
    mov rdi, [g_hstdout]
    mov rsi, rbx
    call write_all
    pop rbx
    ret

; sb_put_timestamp(rdi=sb): "YYYY-MM-DD HH:MM:SS UTC"
sb_put_timestamp:
    push rbx
    push r12
    push r13
    push r14
    push r15
    sub rsp, 16
    mov rbx, rdi
    call os_utc_secs
    xor edx, edx
    mov ecx, 86400
    div rcx                       ; rax = days, rdx = seconds of day
    mov r12, rdx
    add rax, 719468               ; z
    xor edx, edx
    mov ecx, 146097
    div rcx                       ; rax = era, rdx = doe
    mov r13, rax
    mov r14, rdx
    mov rax, r14
    xor edx, edx
    mov ecx, 1460
    div rcx
    mov r8, rax                   ; doe/1460
    mov rax, r14
    xor edx, edx
    mov ecx, 36524
    div rcx
    mov r9, rax                   ; doe/36524
    mov rax, r14
    xor edx, edx
    mov ecx, 146096
    div rcx                       ; rax = doe/146096
    mov rcx, r14
    sub rcx, r8
    add rcx, r9
    sub rcx, rax
    mov rax, rcx
    xor edx, edx
    mov ecx, 365
    div rcx                       ; rax = yoe
    mov r15, rax
    imul r8, r13, 400
    add r8, r15                   ; r8 = y
    mov rax, r15
    shr rax, 2                    ; yoe/4
    mov r9, rax
    mov rax, r15
    xor edx, edx
    mov ecx, 100
    div rcx                       ; rax = yoe/100
    imul rcx, r15, 365
    add rcx, r9
    sub rcx, rax
    sub r14, rcx                  ; r14 = doy
    lea rax, [r14*4+r14]
    add rax, 2
    xor edx, edx
    mov ecx, 153
    div rcx                       ; rax = mp
    mov r9, rax
    imul rax, rax, 153
    add rax, 2
    xor edx, edx
    mov ecx, 5
    div rcx
    sub r14, rax
    inc r14                       ; r14 = day
    lea r10, [r9+3]               ; m = mp+3 or mp-9
    cmp r9, 10
    jb .m_ok
    lea r10, [r9-9]
.m_ok:
    cmp r10, 2
    ja .y_ok
    inc r8
.y_ok:
    mov [rsp], r10                ; month
    mov rdi, rbx
    mov rsi, r8
    call sb_putu
    mov rdi, rbx
    mov esi, '-'
    call sb_putc
    mov rdi, rbx
    mov rsi, [rsp]
    call sb_put2
    mov rdi, rbx
    mov esi, '-'
    call sb_putc
    mov rdi, rbx
    mov rsi, r14
    call sb_put2
    mov rdi, rbx
    mov esi, ' '
    call sb_putc
    mov rax, r12
    xor edx, edx
    mov ecx, 3600
    div rcx
    mov r12, rdx                  ; seconds within the hour
    mov rdi, rbx
    mov rsi, rax
    call sb_put2
    mov rdi, rbx
    mov esi, ':'
    call sb_putc
    mov rax, r12
    xor edx, edx
    mov ecx, 60
    div rcx
    mov r12, rdx
    mov rdi, rbx
    mov rsi, rax
    call sb_put2
    mov rdi, rbx
    mov esi, ':'
    call sb_putc
    mov rdi, rbx
    mov rsi, r12
    call sb_put2
    mov rdi, rbx
    lea rsi, [s_utc]
    call sb_putz
    add rsp, 16
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; lock_acquire(rdi=&lock) / lock_release(rdi=&lock): simple spinlock
lock_acquire:
.spin:
    mov eax, 1
    xchg [rdi], eax
    test eax, eax
    jz .ok
.wait:
    pause
    cmp dword [rdi], 0
    jne .wait
    jmp .spin
.ok:
    ret
lock_release:
    mov dword [rdi], 0
    ret

; parse_u64(rdi=zstr) -> rax (stops at the first non-digit)
parse_u64:
    xor eax, eax
.loop:
    movzx ecx, byte [rdi]
    sub ecx, '0'
    cmp ecx, 9
    ja .done
    imul rax, rax, 10
    add rax, rcx
    inc rdi
    jmp .loop
.done:
    ret

; streq(rdi=zstr a, rsi=zstr b) -> eax = 1 if equal
streq:
.loop:
    movzx eax, byte [rdi]
    movzx ecx, byte [rsi]
    cmp eax, ecx
    jne .no
    test eax, eax
    jz .yes
    inc rdi
    inc rsi
    jmp .loop
.yes:
    mov eax, 1
    ret
.no:
    xor eax, eax
    ret

; strprefix(rdi=text, rsi=key) -> eax = 1 if text starts with key; rdx = len(key)
strprefix:
    xor edx, edx
.loop:
    movzx ecx, byte [rsi+rdx]
    test ecx, ecx
    jz .yes
    cmp cl, [rdi+rdx]
    jne .no
    inc rdx
    jmp .loop
.yes:
    mov eax, 1
    ret
.no:
    xor eax, eax
    ret

; ---------------------------------------------------------------------------
; build_base: sieve the odd numbers below BASE_INIT into g_base_bits
; (bit i <-> 2i+1, set = composite), list the odd primes in g_base_primes,
; and fill g_shift for the fast-path primes (odd primes <= PMAX).
; ---------------------------------------------------------------------------
build_base:
    push rbx
    push r12
    push r13
    mov rbx, [g_base_bits]
    or byte [rbx], 1                     ; 1 is not prime
    lea r11, [mask8]
    mov r12, 1                           ; i = 1  (n = 3)
.outer:
    lea rax, [r12*2+1]                   ; p
    mov rcx, rax
    imul rcx, rax                        ; p*p
    cmp rcx, BASE_INIT
    jae .extract
    mov rdx, r12
    shr rdx, 3
    mov r8d, r12d
    and r8d, 7
    movzx r9d, byte [r11 + r8]
    test byte [rbx + rdx], r9b
    jnz .next
    mov rdx, rcx
    shr rdx, 1                           ; j = (p*p - 1) / 2
.mark:
    cmp rdx, BASE_BITS
    jae .next
    mov r8, rdx
    shr r8, 3
    mov r9d, edx
    and r9d, 7
    movzx r9d, byte [r11 + r9]
    or byte [rbx + r8], r9b
    add rdx, rax
    jmp .mark
.next:
    inc r12
    jmp .outer
.extract:
    xor edi, edi
    mov esi, BASE_BITS
    call extract_primes
    mov qword [g_base_limit], BASE_INIT
    mov r13, [g_base_primes]
    xor ecx, ecx
.fast:
    mov eax, [r13 + rcx*4]
    cmp eax, PMAX
    ja .fdone
    mov edx, PMAX
    sub edx, eax
    shr edx, 1
    lea r8, [g_shift]
    mov [r8 + rcx*4], edx
    inc rcx
    cmp rcx, MAX_FAST
    jb .fast
.fdone:
    mov rax, [g_nfast_opt]               ; --nfast K (testing aid) caps the fast path
    test rax, rax
    jz .nocap
    cmp rax, rcx
    cmovb rcx, rax
.nocap:
    mov [g_n_fast], rcx
    pop r13
    pop r12
    pop rbx
    ret

; mark_odd_multiples(rdi = bitmap, rsi = first bit index, rdx = p, rcx = end bit index)
mark_odd_multiples:
    lea r9, [mask8]
.loop:
    cmp rsi, rcx
    jae .done
    mov rax, rsi
    shr rax, 3
    mov r8d, esi
    and r8d, 7
    movzx r8d, byte [r9 + r8]
    or byte [rdi + rax], r8b
    add rsi, rdx
    jmp .loop
.done:
    ret

; extract_primes(rdi = first bit index, rsi = end bit index; both multiples
; of 64): append the odd primes of that bitmap range to g_base_primes.
extract_primes:
    push rbx
    push r12
    mov rbx, [g_base_bits]
    mov r12, [g_base_primes]
    mov r9, [g_n_base]
    mov rcx, rdi
    shr rcx, 6
    shr rsi, 6
.eq:
    cmp rcx, rsi
    jae .done
    mov rax, [rbx + rcx*8]
    not rax                              ; set bits = primes
.ebits:
    test rax, rax
    jz .enext
    tzcnt rdx, rax
    mov r8, rcx
    shl r8, 7
    lea r8, [r8 + rdx*2 + 1]             ; n = 128*word + 2*bit + 1
    mov [r12 + r9*4], r8d
    inc r9
    lea rdx, [rax-1]
    and rax, rdx                         ; clear the lowest set bit (no BMI needed)
    jmp .ebits
.enext:
    inc rcx
    jmp .eq
.done:
    mov [g_n_base], r9                   ; published after the entries (x86 stores are ordered)
    pop r12
    pop rbx
    ret

; grow_base(rdi = s): extend the base so that every prime <= s is listed, by
; doubling the sieved range (s < 2^32, so the range never passes BASE_MAX).
; Other threads keep reading the unchanged prefix meanwhile.  Happens at
; N = 2^52, 2^54, ... 2^64: a handful of times in the life of a run.
grow_base:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    mov r12, rdi
    lea rdi, [g_grow_lock]
    call lock_acquire
    mov rbx, [g_base_limit]              ; L
    cmp r12, rbx
    jb .unlock                           ; another thread already did it
    mov r13, rbx
.dbl:
    shl r13, 1                           ; new limit
    cmp r13, r12
    jbe .dbl
    mov rdi, [g_base_bits]               ; make the new bitmap / list ranges usable (Windows)
    mov rax, rbx
    shr rax, 4
    add rdi, rax
    mov rsi, r13
    sub rsi, rbx
    shr rsi, 4
    call os_commit
    mov rdi, [g_base_primes]
    mov rax, rbx
    shr rax, 2
    add rdi, rax
    mov rsi, r13
    sub rsi, rbx
    shr rsi, 2
    call os_commit
    mov r14, [g_base_primes]
    xor ebp, ebp                         ; sieving primes: p*p < new limit  (p <= 65536 < L)
.mark:
    mov ecx, [r14 + rbp*4]
    mov rax, rcx
    imul rax, rcx                        ; p*p
    cmp rax, r13
    jae .extract
    cmp rax, rbx
    jae .from_pp
    mov rax, rbx                         ; first odd multiple of p >= L (L is a power of two,
    xor edx, edx                         ; so it is never a multiple of the odd p)
    div rcx
    inc rax
    test al, 1
    jnz .mult
    inc rax
.mult:
    imul rax, rcx
.from_pp:
    shr rax, 1                           ; bit index of that odd number
    mov rsi, rax
    mov rdx, rcx
    mov rcx, r13
    shr rcx, 1
    mov rdi, [g_base_bits]
    call mark_odd_multiples
    inc rbp
    jmp .mark
.extract:
    mov rdi, rbx
    shr rdi, 1
    mov rsi, r13
    shr rsi, 1
    call extract_primes
    mov [g_base_limit], r13
.unlock:
    lea rdi, [g_grow_lock]
    call lock_release
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret

; base_composite(rdi = odd n < g_base_limit) -> eax = 1 if composite
base_composite:
    shr rdi, 1
    mov rax, rdi
    shr rax, 6
    mov rcx, [g_base_bits]
    mov rax, [rcx + rax*8]
    bt rax, rdi
    setc al
    movzx eax, al
    ret

; pi_small(rdi = x, 2 <= x < g_base_limit) -> rax = number of primes <= x
pi_small:
    lea rcx, [rdi-1]
    shr rcx, 1
    inc rcx                              ; bits to examine: indices 0..(x-1)/2
    push rbx
    push r12
    push r13
    mov r12, rdi
    mov r13, rcx
    and r13d, 63                         ; bits in the partial last word
    mov rdi, [g_base_bits]
    mov rsi, rcx
    shr rsi, 6                           ; full qwords
    mov rbx, rsi
    call popcnt_words
    test r13, r13
    jz .done
    mov rdi, [g_base_bits]
    mov rdx, [rdi + rbx*8]
    mov rcx, r13
    mov r8, 1
    shl r8, cl
    dec r8
    and rdx, r8
    push rax
    push rdx
    mov rdi, rsp
    mov esi, 1
    call popcnt_words
    pop rdx
    pop rcx
    add rax, rcx
.done:
    mov rdi, r12
    lea rdx, [rdi-1]
    shr rdx, 1
    inc rdx                              ; total bits examined
    sub rdx, rax                         ; clear bits = odd primes
    lea rax, [rdx+1]                     ; + the prime 2
    pop r13
    pop r12
    pop rbx
    ret

; popcnt_words(rdi = qwords, rsi = count) -> rax: hardware POPCNT when the
; CPU has it, otherwise a bit-twiddling fallback (SWAR).
popcnt_words:
    xor eax, eax
    test rsi, rsi
    jz .ret
    cmp byte [g_have_popcnt], 0
    je .soft
.hw:
    popcnt rdx, [rdi]
    add rax, rdx
    add rdi, 8
    dec rsi
    jnz .hw
    ret
.soft:
    mov r8, 0x5555555555555555
    mov r9, 0x3333333333333333
    mov r10, 0x0F0F0F0F0F0F0F0F
    mov r11, 0x0101010101010101
.sw:
    mov rdx, [rdi]
    mov rcx, rdx
    shr rcx, 1
    and rcx, r8
    sub rdx, rcx
    mov rcx, rdx
    and rcx, r9
    shr rdx, 2
    and rdx, r9
    add rdx, rcx
    mov rcx, rdx
    shr rcx, 4
    add rdx, rcx
    and rdx, r10
    imul rdx, r11
    shr rdx, 56
    add rax, rdx
    add rdi, 8
    dec rsi
    jnz .sw
.ret:
    ret

; count_base_le(rdi = s) -> rax = number of base primes <= s (binary search)
count_base_le:
    mov rsi, [g_base_primes]
    xor eax, eax                         ; lo
    mov rcx, [g_n_base]                  ; hi
.loop:
    cmp rax, rcx
    jae .done
    lea rdx, [rax+rcx]
    shr rdx, 1
    mov r8d, [rsi + rdx*4]
    cmp r8, rdi
    ja .left
    lea rax, [rdx+1]
    jmp .loop
.left:
    mov rcx, rdx
    jmp .loop
.done:
    ret

; isqrt(rdi = n) -> rax = floor(sqrt(n)) for any 64-bit n (bitwise search;
; every candidate is below 2^32, so its square cannot overflow)
isqrt:
    xor eax, eax
    mov ecx, 1 << 31
.loop:
    lea rdx, [rax + rcx]
    mov r8, rdx
    imul r8, rdx
    cmp r8, rdi
    ja .skip
    mov rax, rdx
.skip:
    shr ecx, 1
    jnz .loop
    ret

; ---------------------------------------------------------------------------
; Deterministic Miller-Rabin.  Witness sets by size (Jaeschke; Sorenson &
; Webster): {2,3,5,7} < 3,215,031,751; {..13} < 3,474,749,660,383;
; {..17} < 341,550,071,728,321; {..23} < 3,825,123,056,546,413,051;
; {..37} < 3.18e23 which covers every 64-bit integer.
; ---------------------------------------------------------------------------
; powmod(rdi=base, rsi=exp, rdx=mod) -> rax
powmod:
    mov rcx, rdx
    mov r8, rsi
    mov r9, rdi
    mov r10d, 1
.loop:
    test r8, r8
    jz .done
    test r8b, 1
    jz .sq
    mov rax, r10
    mul r9
    div rcx
    mov r10, rdx
.sq:
    mov rax, r9
    mul r9
    div rcx
    mov r9, rdx
    shr r8, 1
    jmp .loop
.done:
    mov rax, r10
    ret

; is_prime_mr(rdi=n) -> eax = 1 if prime
is_prime_mr:
    push rbx
    push r12
    push r13
    push r14
    push r15
    mov rbx, rdi
    cmp rbx, 2
    jb .no
    cmp rbx, 3
    jbe .yes
    test bl, 1
    jz .no
    cmp rbx, 5
    je .yes
    mov rax, rbx
    xor edx, edx
    mov ecx, 3
    div rcx
    test rdx, rdx
    jz .no
    mov rax, rbx
    xor edx, edx
    mov ecx, 5
    div rcx
    test rdx, rdx
    jz .no
    lea r12, [rbx-1]
    tzcnt rcx, r12
    mov r13, rcx                         ; r
    shr r12, cl                          ; d
    mov r14d, 12
    mov rax, 3825123056546413051
    cmp rbx, rax
    jae .have
    mov r14d, 9
    mov rax, 341550071728321
    cmp rbx, rax
    jae .have
    mov r14d, 7
    mov rax, 3474749660383
    cmp rbx, rax
    jae .have
    mov r14d, 6
    mov rax, 3215031751
    cmp rbx, rax
    jae .have
    mov r14d, 4
.have:
    xor r15d, r15d
.wit:
    cmp r15, r14
    jae .yes
    lea rdi, [mr_witnesses]
    movzx edi, byte [rdi + r15]
    cmp rdi, rbx
    jae .wnext
    mov rsi, r12
    mov rdx, rbx
    call powmod
    cmp rax, 1
    je .wnext
    lea rdx, [rbx-1]
    cmp rax, rdx
    je .wnext
    mov r8, r13
    dec r8                               ; r-1 squarings allowed
    mov rcx, rbx
.sq:
    test r8, r8
    jz .no
    mul rax
    div rcx
    mov rax, rdx
    dec r8
    lea rdx, [rbx-1]
    cmp rax, rdx
    jne .sq
.wnext:
    inc r15
    jmp .wit
.yes:
    mov eax, 1
    jmp .ret
.no:
    xor eax, eax
.ret:
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; fallback(rdi = N): exhaustive search with p > PMAX, p <= N/2.
; Returns rax = number of odd p tried (0 = no partition found), rdx = p.
; ---------------------------------------------------------------------------
fallback:
    push rbx
    push r12
    push r13
    push r14
    mov rbx, rdi
    mov r12, rdi
    shr r12, 1
    mov r13d, PMAX + 2
    xor r14d, r14d
.loop:
    cmp r13, r12
    ja .none
    inc r14
    cmp r13, [g_base_limit]
    jae .mr
    mov rdi, r13
    call base_composite
    test eax, eax
    jnz .next
    jmp .pprime
.mr:
    mov rdi, r13
    call is_prime_mr
    test eax, eax
    jz .next
.pprime:
    mov rdi, rbx
    sub rdi, r13
    call is_prime_mr
    test eax, eax
    jz .next
    mov rax, r14
    mov rdx, r13
    jmp .ret
.next:
    add r13, 2
    jmp .loop
.none:
    xor eax, eax
    xor edx, edx
.ret:
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; Records and violations (text output).
; ---------------------------------------------------------------------------
; write_record(rdi=header, rsi=N, rdx=depth): append to interesting_cases.txt
write_record:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, rsi
    mov r13, rdx
    lea rdi, [g_msb]
    mov qword [rdi+8], 0
    mov rsi, rbx
    call sb_putz
    lea rdi, [g_msb]
    lea rsi, [s_rec_num]
    call sb_putz
    lea rdi, [g_msb]
    mov rsi, r12
    call sb_putu
    lea rdi, [g_msb]
    lea rsi, [s_rec_chk]
    call sb_putz
    lea rdi, [g_msb]
    mov rsi, r13
    call sb_putu
    lea rdi, [g_msb]
    lea rsi, [s_rec_ts]
    call sb_putz
    lea rdi, [g_msb]
    call sb_put_timestamp
    lea rdi, [g_msb]
    lea rsi, [s_rec_end]
    call sb_putz
    lea rdi, [g_msb]
    mov rsi, [g_fd_int]
    call sb_flush
    pop r13
    pop r12
    pop rbx
    ret

; record_fast(rdi=N, rsi=depth) / record_fb(rdi=N, rsi=depth)
record_fast:
    mov [g_max_N], rdi
    mov [g_max_depth], rsi
    mov rdx, rsi
    mov rsi, rdi
    lea rdi, [s_rec_fast]
    jmp write_record
record_fb:
    mov [g_fb_max_N], rdi
    mov [g_fb_max_depth], rsi
    mov rdx, rsi
    mov rsi, rdi
    lea rdi, [s_rec_fb]
    jmp write_record

; write_violation(rdi=N): violations.txt line + console message (any thread)
write_violation:
    push rbx
    mov rbx, rdi
    lea rdi, [g_vlock]
    call lock_acquire
    lea rdi, [g_vsb]
    mov qword [rdi+8], 0
    lea rsi, [s_vio1]
    call sb_putz
    lea rdi, [g_vsb]
    mov rsi, rbx
    call sb_putu
    lea rdi, [g_vsb]
    lea rsi, [s_vio2]
    call sb_putz
    lea rdi, [g_vsb]
    mov rsi, [g_fd_vio]
    call sb_flush
    lea rdi, [g_vsb]
    lea rsi, [s_vio_out1]
    call sb_putz
    lea rdi, [g_vsb]
    mov rsi, rbx
    call sb_putu
    lea rdi, [g_vsb]
    lea rsi, [s_vio_out2]
    call sb_putz
    lea rdi, [g_vsb]
    mov rsi, [g_hstdout]
    call sb_flush
    lea rdi, [g_vlock]
    call lock_release
    pop rbx
    ret

; log_line(rdi=sb, rsi=N, rdx=p): "N = p + q" into a --log buffer, flushing
; to goldbach.txt when the buffer is nearly full.
log_line:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, rsi
    mov r13, rdx
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_eq]
    call sb_putz
    mov rdi, rbx
    mov rsi, r13
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_plus]
    call sb_putz
    mov rdi, rbx
    mov rsi, r12
    sub rsi, r13
    call sb_putu
    mov rdi, rbx
    mov esi, 10
    call sb_putc
    mov rax, [rbx+16]
    sub rax, 80
    cmp [rbx+8], rax
    jb .ok
    mov rdi, rbx
    mov rsi, [g_fd_log]
    call sb_flush
.ok:
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; small_path(rdi = N_from): verify even N in [N_from, SMALL_END) on the main
; thread with direct bitmap lookups (handles the p <= N/2 cases near 0).
; ---------------------------------------------------------------------------
small_path:
    push rbx
    push r12
    push r13
    push r14
    push r15
    mov rbx, rdi
.N:
    cmp rbx, SMALL_END
    jae .done
    cmp rbx, 4
    jne .general
    mov r12d, 1                          ; 4 = 2 + 2: one check
    mov r13d, 2
    jmp .found
.general:
    mov r14, rbx
    shr r14, 1                           ; N/2
    xor r15d, r15d                       ; k
.k:
    cmp r15, [g_n_fast]
    jae .fallback
    mov rcx, [g_base_primes]
    mov r13d, [rcx + r15*4]              ; p
    cmp r13, r14
    ja .fallback
    mov rdi, rbx
    sub rdi, r13                         ; q
    call base_composite
    test eax, eax
    jz .hit
    inc r15
    jmp .k
.hit:
    lea r12, [r15+2]                     ; depth = pi(p)
.found:
    cmp r12, [g_max_depth]
    jbe .log
    mov rdi, rbx
    mov rsi, r12
    call record_fast
    jmp .log
.fallback:
    mov rdi, rbx
    call fallback
    inc qword [g_fb_count]
    test rax, rax
    jz .viol
    mov r13, rdx
    cmp rax, [g_fb_max_depth]
    jbe .log
    mov rdi, rbx
    mov rsi, rax
    call record_fb
    jmp .log
.viol:
    inc qword [g_violations]
    mov rdi, rbx
    call write_violation
    jmp .next
.log:
    cmp qword [g_log_mode], 0
    je .next
    lea rdi, [g_logsb]
    mov rsi, rbx
    mov rdx, r13
    call log_line
.next:
    add rbx, 2
    jmp .N
.done:
    cmp qword [g_log_mode], 0
    je .ret
    lea rdi, [g_logsb]
    mov rsi, [g_fd_log]
    call sb_flush
.ret:
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; sieve_segment(edi = 1 for the first segment of a chunk).  r15 = ctx.
; Marks composite odd numbers sb+2i (i < W) in the context bitmap, carrying
; each base prime's next index across the segments of a chunk.
; ---------------------------------------------------------------------------
sieve_segment:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    mov rbx, r15                         ; bitmap base (CTX_COMP = 0)
    mov qword [r15 + HDR_JBIAS], HALFP   ; stored index = j_final - W; next segment: + HALFP
    test edi, edi
    jz .copy
    mov qword [r15 + HDR_JBIAS], 0       ; first segment: stored index is the index itself
    mov rdi, rbx                         ; fresh bitmap: clear, pad = all ones
    mov ecx, WQ
    xor eax, eax
    rep stosq
    mov ecx, WPAD
    mov rax, -1
    rep stosq
    mov r12, [r15 + HDR_SEGBASE]
    mov r13, [g_base_primes]
    lea r14, [r15 + CTX_NEXTJ]
    xor ebp, ebp
.init:                                   ; index of the first odd multiple of p >= max(sb, p*p)
    cmp rbp, [r15 + HDR_NUSE]
    jae .sieve
    mov ecx, [r13 + rbp*4]
    mov rax, rcx
    imul rax, rcx                        ; p*p (p < 2^32: no overflow)
    cmp rax, r12
    jb .div
    sub rax, r12
    shr rax, 1
    jmp .store
.div:
    mov rax, r12
    xor edx, edx
    div rcx                              ; sb / p, sb mod p   (no sb + p - 1: it could pass 2^64)
    test rdx, rdx
    jz .mult                             ; sb is itself an odd multiple (odd / odd => odd quotient)
    inc rax
    test al, 1
    jnz .mult
    inc rax
.mult:
    mul rcx                              ; the multiple; CF set when it lies beyond 2^64
    jc .none
    sub rax, r12
    shr rax, 1
    jmp .store
.none:
    mov eax, 0xFFFFFFFF                  ; stays >= W in every segment of this chunk: no marks
.store:
    mov [r14 + rbp*4], eax
    inc rbp
    jmp .init
.copy:                                   ; later segments: keep the overlap, clear the rest
    lea rsi, [rbx + EQ*8]
    mov rdi, rbx
    mov ecx, HALFP/64
    rep movsq
    mov ecx, WQ - HALFP/64
    xor eax, eax
    rep stosq
.sieve:
    mov r13, [g_base_primes]
    lea r14, [r15 + CTX_NEXTJ]
    mov rbp, [r15 + HDR_NUSE]
    xor r12d, r12d
.pk:
    cmp r12, rbp
    jae .done
    mov ecx, [r13 + r12*4]               ; p
    mov esi, [r14 + r12*4]
    add rsi, [r15 + HDR_JBIAS]           ; j = next index in this segment
    cmp rsi, W
    jae .storej
    cmp rcx, W/8
    jae sieve_tail
    mov r8, W
    lea rax, [rcx*8]
    sub r8, rax
    add r8, rcx                          ; lim = W - 7p: 8 marks fit while j < lim
    cmp rsi, r8
    jae sieve_tail
    mov r9, rsi
    shr r9, 3
    add r9, rbx                          ; byte pointer of mark 0
    mov r10, rcx
    shr r10, 3                           ; q = p/8
    lea r11, [r10 + r10*2]               ; 3q
    lea rdx, [r10 + r10*4]               ; 5q
    lea rdi, [r11 + r10*4]               ; 7q
    mov eax, esi
    and eax, 7
    shl eax, 2
    mov esi, ecx
    and esi, 7
    shr esi, 1
    or eax, esi                          ; case = (j&7)*4 + (p&7)/2
    lea rsi, [m8_table]
    jmp [rsi + rax*8]
.storej:
    sub rsi, W                           ; j_final - W < p: always fits 32 bits
    mov [r14 + r12*4], esi
    inc r12
    jmp .pk
.done:
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret

; Eight marks per iteration for prime p = 8q + RR starting at bit B of the
; current byte: mark k lives at byte k*q + ((B + k*RR) >> 3), bit (B + k*RR) & 7.
%macro M8CASE 2
m8_%1_%2:
    lea r8, [r8 + 7 - %1]
    shr r8, 3
    add r8, rbx                          ; pointer limit equivalent to j < lim
m8_%1_%2_l:
    or byte [r9], (1 << %1)
    or byte [r9 + r10 + ((%1 + %2) >> 3)], (1 << ((%1 + %2) & 7))
    or byte [r9 + r10*2 + ((%1 + 2*%2) >> 3)], (1 << ((%1 + 2*%2) & 7))
    or byte [r9 + r11 + ((%1 + 3*%2) >> 3)], (1 << ((%1 + 3*%2) & 7))
    or byte [r9 + r10*4 + ((%1 + 4*%2) >> 3)], (1 << ((%1 + 4*%2) & 7))
    or byte [r9 + rdx + ((%1 + 5*%2) >> 3)], (1 << ((%1 + 5*%2) & 7))
    or byte [r9 + r11*2 + ((%1 + 6*%2) >> 3)], (1 << ((%1 + 6*%2) & 7))
    or byte [r9 + rdi + ((%1 + 7*%2) >> 3)], (1 << ((%1 + 7*%2) & 7))
    add r9, rcx                          ; 8 marks = p bytes
    cmp r9, r8
    jb m8_%1_%2_l
    mov rsi, r9
    sub rsi, rbx
    shl rsi, 3
    add rsi, %1                          ; back to a bit index
    jmp sieve_tail
%endmacro

M8CASE 0,1
M8CASE 0,3
M8CASE 0,5
M8CASE 0,7
M8CASE 1,1
M8CASE 1,3
M8CASE 1,5
M8CASE 1,7
M8CASE 2,1
M8CASE 2,3
M8CASE 2,5
M8CASE 2,7
M8CASE 3,1
M8CASE 3,3
M8CASE 3,5
M8CASE 3,7
M8CASE 4,1
M8CASE 4,3
M8CASE 4,5
M8CASE 4,7
M8CASE 5,1
M8CASE 5,3
M8CASE 5,5
M8CASE 5,7
M8CASE 6,1
M8CASE 6,3
M8CASE 6,5
M8CASE 6,7
M8CASE 7,1
M8CASE 7,3
M8CASE 7,5
M8CASE 7,7

section .rodata
align 8
m8_table:   dq m8_0_1, m8_0_3, m8_0_5, m8_0_7, m8_1_1, m8_1_3, m8_1_5, m8_1_7
            dq m8_2_1, m8_2_3, m8_2_5, m8_2_7, m8_3_1, m8_3_3, m8_3_5, m8_3_7
            dq m8_4_1, m8_4_3, m8_4_5, m8_4_7, m8_5_1, m8_5_3, m8_5_5, m8_5_7
            dq m8_6_1, m8_6_3, m8_6_5, m8_6_7, m8_7_1, m8_7_3, m8_7_5, m8_7_7
section .text

; remaining marks one at a time (rsi = j, rcx = p, rbx = bitmap, r12 = k)
sieve_tail:
    lea r8, [mask8]
.loop:
    cmp rsi, W
    jae .store
    mov rax, rsi
    shr rax, 3
    mov edx, esi
    and edx, 7
    movzx edx, byte [r8 + rdx]
    or byte [rbx + rax], dl
    add rsi, rcx
    jmp .loop
.store:
    sub rsi, W
    mov [r14 + r12*4], esi
    inc r12
    jmp sieve_segment.pk

; ---------------------------------------------------------------------------
; vec_pass(rdi = &comp[a], rsi = unres, edx = b): one word-parallel pass.
; For every 4 qwords: shifted = comp >> (64a+b) (bit j = composite(N_j - p));
; hits = unres & ~shifted; unres &= shifted.
; Returns rax = index of the first hit (or -1), rdx = 1 if anything remains.
; ---------------------------------------------------------------------------
vec_pass_avx2:
    vmovq xmm6, rdx
    mov ecx, 64
    sub ecx, edx
    vmovq xmm7, rcx
    vpxor ymm4, ymm4, ymm4
    mov r8, -1
    mov ecx, EQ/4
    xor r9d, r9d
    sub rsp, 40
.loop:
    vmovdqu ymm0, [rdi]
    vmovdqu ymm1, [rdi+8]
    vpsrlq ymm0, ymm0, xmm6
    vpsllq ymm1, ymm1, xmm7
    vpor ymm0, ymm0, ymm1
    vmovdqa ymm2, [rsi]
    vpandn ymm3, ymm0, ymm2
    vptest ymm3, ymm3
    jz .nohit
    vpand ymm2, ymm2, ymm0
    vmovdqa [rsi], ymm2
    test r8, r8
    jns .nohit
    vmovdqu [rsp], ymm3
    xor r10d, r10d
.find:
    mov rax, [rsp + r10*8]
    test rax, rax
    jnz .got
    inc r10
    jmp .find
.got:
    tzcnt rax, rax
    lea r8, [r10 + r9*4]
    shl r8, 6
    add r8, rax
.nohit:
    vpor ymm4, ymm4, ymm2
    add rdi, 32
    add rsi, 32
    inc r9
    dec ecx
    jnz .loop
    add rsp, 40
    vptest ymm4, ymm4
    setnz dl
    movzx edx, dl
    mov rax, r8
    vzeroupper
    ret

; vec_pass_scalar: same contract, plain 64-bit code for CPUs without AVX2.
vec_pass_scalar:
    mov ecx, edx                         ; cl = b
    mov r8, -1                           ; first hit
    xor r9d, r9d                         ; OR of the remaining words
    xor r10d, r10d                       ; word index
.loop:
    mov rax, [rdi + r10*8]
    mov rdx, [rdi + r10*8 + 8]
    shrd rax, rdx, cl                    ; shifted composite bits (b = 0 leaves rax)
    mov rdx, [rsi + r10*8]               ; unresolved
    mov r11, rax
    not r11
    and r11, rdx                         ; hits = unres & ~composite
    jz .nohit
    and rdx, rax
    mov [rsi + r10*8], rdx
    test r8, r8
    jns .nohit
    tzcnt r8, r11
    mov r11, r10
    shl r11, 6
    add r8, r11
.nohit:
    or r9, rdx
    inc r10
    cmp r10, EQ
    jb .loop
    xor edx, edx
    test r9, r9
    setnz dl
    mov rax, r8
    ret

; count_unres() -> rax = unresolved bits remaining.  r15 = ctx.
count_unres:
    lea rdi, [r15 + CTX_UNRES]
    mov esi, EQ
    jmp popcnt_words

; count_segment_primes() -> rax = odd primes among N_j - 1, j < E.  r15 = ctx.
count_segment_primes:
    lea rdi, [r15 + HALFP/8]
    mov esi, WQ - HALFP/64
    call popcnt_words
    mov rcx, E
    sub rcx, rax
    mov rax, rcx
    ret

; resolve_one(rdi = j, rsi = first prime index to try).  r15 = ctx.
resolve_one:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov r12, rsi
    mov r13, [g_n_fast]
.k:
    cmp r12, r13
    jae .fb
    lea rax, [g_shift]
    mov eax, [rax + r12*4]
    add rax, rbx
    mov rcx, rax
    shr rcx, 6
    mov rcx, [r15 + rcx*8]
    bt rcx, rax
    jnc .hit
    inc r12
    jmp .k
.hit:
    lea rax, [r12+2]
    mov rcx, [r15 + HDR_SEGBASE]
    lea rcx, [rcx + rbx*2 + PMAX]        ; N
    cmp qword [r15 + CTX_FIRSTN + rax*8], 0
    jne .seen
    mov [r15 + CTX_FIRSTN + rax*8], rcx  ; j ascends, so the first one is the smallest N
.seen:
    cmp rax, [r15 + HDR_SEGMAXD]
    jbe .ret
    mov [r15 + HDR_SEGMAXD], rax
    mov [r15 + HDR_SEGMAXN], rcx
    jmp .ret
.fb:
    mov rdi, [r15 + HDR_SEGBASE]
    lea rdi, [rdi + rbx*2 + PMAX]
    mov rbx, rdi
    call fallback
    inc qword [r15 + HDR_FBC]
    test rax, rax
    jz .viol
    mov rdi, rbx
    mov rsi, rax
    call fb_record
    jmp .ret
.viol:
    inc qword [r15 + HDR_VIO]
    mov rdi, rbx
    call write_violation
.ret:
    pop r13
    pop r12
    pop rbx
    ret

; fb_record(rdi = N, rsi = fallback depth): keep the chunk's running maxima
; of the fallback depth (N ascends within a chunk).  r15 = ctx.
fb_record:
    cmp rsi, [r15 + HDR_FBD]
    jbe .ret
    mov [r15 + HDR_FBD], rsi
    mov rax, [r15 + HDR_NFB]
    cmp rax, MAXFBREC
    jae .ret
    mov rcx, [r15 + HDR_SLOT]
    shl rax, 4
    mov [rcx + rax + SLOT_FBRECS], rdi
    mov [rcx + rax + SLOT_FBRECS + 8], rsi
    inc qword [r15 + HDR_NFB]
.ret:
    ret

; seg_records(): turn the segment's first-N-per-depth table into the exact
; running maxima of depth in order of N, continuing the chunk's running
; maximum, and append them to the slot.  (N_d, d) is a record iff no deeper
; depth occurs at a smaller N: scan depths downwards keeping the minimum N.
; r15 = ctx.  Leaves the table cleared for the next segment.
seg_records:
    mov rcx, [g_n_fast]
    inc rcx                              ; deepest possible depth
    mov rdx, -1                          ; minimum N seen so far
.down:
    cmp rcx, 2
    jb .up_init
    mov rax, [r15 + CTX_FIRSTN + rcx*8]
    test rax, rax
    jz .dnext
    cmp rax, rdx
    jae .drop
    mov rdx, rax
    jmp .dnext
.drop:
    mov qword [r15 + CTX_FIRSTN + rcx*8], 0
.dnext:
    dec rcx
    jmp .down
.up_init:
    mov ecx, 2
.up:
    cmp rcx, [g_n_fast]
    ja .done
    mov rax, [r15 + CTX_FIRSTN + rcx*8]
    test rax, rax
    jz .unext
    mov qword [r15 + CTX_FIRSTN + rcx*8], 0
    cmp rcx, [r15 + HDR_MAXD]
    jbe .unext
    mov [r15 + HDR_MAXD], rcx
    mov rdx, [r15 + HDR_NREC]
    cmp rdx, MAXREC
    jae .unext
    mov rdi, [r15 + HDR_SLOT]
    shl rdx, 4
    mov [rdi + rdx + SLOT_RECS], rax
    mov [rdi + rdx + SLOT_RECS + 8], rcx
    inc qword [r15 + HDR_NREC]
.unext:
    inc rcx
    jmp .up
.done:
    ret

; ---------------------------------------------------------------------------
; goldbach_segment(): verify the E even numbers of the current segment.
; Dense word-parallel passes, then the sparse finisher.  r15 = ctx.
; ---------------------------------------------------------------------------
goldbach_segment:
    push rbx
    push r12
    push r13
    push r14
    mov qword [r15 + HDR_SEGMAXD], 0
    mov qword [r15 + HDR_SEGMAXN], 0
    lea rdi, [r15 + CTX_UNRES]
    mov ecx, EQ
    mov rax, -1
    rep stosq
    mov ecx, 4
    xor eax, eax
    rep stosq
    xor ebx, ebx                         ; k = odd prime index
.dense:
    cmp rbx, [g_n_fast]
    jae .sparse
    lea rdx, [g_shift]
    mov edx, [rdx + rbx*4]
    mov rax, rdx
    shr rax, 6
    and edx, 63
    lea rdi, [r15 + rax*8]
    lea rsi, [r15 + CTX_UNRES]
    call [g_vec_pass]                    ; AVX2 or scalar, chosen at startup
    test rax, rax
    js .nohit
    lea rcx, [rbx + 2]                   ; depth of this pass
    mov [r15 + HDR_SEGMAXD], rcx
    mov rdi, [r15 + HDR_SEGBASE]
    lea rdi, [rdi + rax*2 + PMAX]        ; first N resolved at this depth
    mov [r15 + HDR_SEGMAXN], rdi
    mov [r15 + CTX_FIRSTN + rcx*8], rdi
.nohit:
    inc rbx
    test rdx, rdx
    jz .done
    test bl, 15
    jnz .dense
    call count_unres
    cmp rax, SPARSE_THRESH
    jae .dense
.sparse:
    lea r12, [r15 + CTX_UNRES]
    xor r13d, r13d
.sw:
    cmp r13, EQ
    jae .done
    mov r14, [r12 + r13*8]
.sbit:
    test r14, r14
    jz .swnext
    tzcnt rax, r14
    mov rdi, r13
    shl rdi, 6
    add rdi, rax
    mov rsi, rbx
    call resolve_one
    lea rax, [r14-1]
    and r14, rax
    jmp .sbit
.swnext:
    inc r13
    jmp .sw
.done:
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; goldbach_segment_scalar(): straightforward per-N version of the above.
; Used for --log (emits "N = p + q" lines) and --check.  r15 = ctx.
; ---------------------------------------------------------------------------
goldbach_segment_scalar:
    push rbx
    push r12
    push r13
    push r14
    mov qword [r15 + HDR_SEGMAXD], 0
    mov qword [r15 + HDR_SEGMAXN], 0
    xor ebx, ebx                         ; j
.j:
    cmp rbx, E
    jae .done
    xor r12d, r12d                       ; k
.k:
    cmp r12, [g_n_fast]
    jae .fb
    lea rax, [g_shift]
    mov eax, [rax + r12*4]
    add rax, rbx
    mov rcx, rax
    shr rcx, 6
    mov rcx, [r15 + rcx*8]
    bt rcx, rax
    jnc .hit
    inc r12
    jmp .k
.hit:
    lea rax, [r12+2]
    mov rcx, [r15 + HDR_SEGBASE]
    lea rcx, [rcx + rbx*2 + PMAX]        ; N
    cmp qword [r15 + CTX_FIRSTN + rax*8], 0
    jne .seen
    mov [r15 + CTX_FIRSTN + rax*8], rcx
.seen:
    cmp rax, [r15 + HDR_SEGMAXD]
    jbe .lg
    mov [r15 + HDR_SEGMAXD], rax
    mov [r15 + HDR_SEGMAXN], rcx
.lg:
    cmp qword [g_log_mode], 0
    je .next
    mov rcx, [g_base_primes]
    mov edx, [rcx + r12*4]
    jmp .log
.fb:
    mov rdi, [r15 + HDR_SEGBASE]
    lea rdi, [rdi + rbx*2 + PMAX]
    mov r13, rdi
    call fallback
    inc qword [r15 + HDR_FBC]
    test rax, rax
    jz .viol
    mov r14, rdx
    mov rdi, r13
    mov rsi, rax
    call fb_record
.fblog:
    cmp qword [g_log_mode], 0
    je .next
    mov rdx, r14
.log:
    mov rsi, [r15 + HDR_SEGBASE]
    lea rsi, [rsi + rbx*2 + PMAX]
    lea rdi, [r15 + HDR_LOGSB]
    call log_line
    jmp .next
.viol:
    inc qword [r15 + HDR_VIO]
    mov rdi, r13
    call write_violation
.next:
    inc rbx
    jmp .j
.done:
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; process_chunk(rdi = chunk index) -> eax = 1 when the chunk was completed.
; r15 = ctx.  Writes the chunk's statistics into its ring slot.
; ---------------------------------------------------------------------------
process_chunk:
    push rbx
    push r12
    push r13
    mov rbx, rdi
    mov rax, CHUNK
    mul rbx
    add rax, [g_N0]
    sub rax, PMAX
    mov r12, rax                         ; sb0 = first odd number of segment 0
    lea rdi, [r12 + SEG_LAST_OFF]        ; last odd number sieved (< 2^64: checked by the caller)
    call isqrt
    mov r13, rax
    cmp rax, [g_base_limit]
    jb .base_ok
    mov rdi, rax
    call grow_base
.base_ok:
    mov rdi, r13
    call count_base_le
    mov [r15 + HDR_NUSE], rax
    shl rax, 2                           ; bytes of next_j in use: make them usable (Windows)
    cmp rax, [r15 + HDR_COMMITTED]
    jbe .committed
    add rax, 0x3FFFFF
    and rax, -0x400000                   ; 4 MB steps
    mov rsi, rax
    sub rsi, [r15 + HDR_COMMITTED]
    lea rdi, [r15 + CTX_NEXTJ]
    add rdi, [r15 + HDR_COMMITTED]
    mov [r15 + HDR_COMMITTED], rax
    call os_commit
.committed:
    mov eax, ebx                         ; this chunk's ring slot (free: see worker_entry)
    and eax, RING-1
    shl eax, 13
    lea rcx, [g_slots]
    add rax, rcx
    mov [r15 + HDR_SLOT], rax
    xor eax, eax
    mov [r15 + HDR_MAXD], rax
    mov [r15 + HDR_FBC], rax
    mov [r15 + HDR_FBD], rax
    mov [r15 + HDR_VIO], rax
    mov [r15 + HDR_PC], rax
    mov [r15 + HDR_NREC], rax
    mov [r15 + HDR_NFB], rax
    xor r13d, r13d                       ; segment index
.seg:
    cmp r13, R
    jae .store
    imul rax, r13, 2*E
    add rax, r12
    mov [r15 + HDR_SEGBASE], rax
    xor edi, edi
    test r13, r13
    setz dil
    call sieve_segment
    cmp qword [g_log_mode], 0
    jne .scalar
    call goldbach_segment
    cmp qword [g_check_mode], 0
    je .merge
    mov rax, [r15 + HDR_SEGMAXD]         ; --check: run the scalar version too and compare
    mov [r15 + HDR_CHKD], rax
    mov rax, [r15 + HDR_SEGMAXN]
    mov [r15 + HDR_CHKN], rax
    call goldbach_segment_scalar
    mov rax, [r15 + HDR_SEGMAXD]
    cmp rax, [r15 + HDR_CHKD]
    jne .mismatch
    mov rax, [r15 + HDR_SEGMAXN]
    cmp rax, [r15 + HDR_CHKN]
    jne .mismatch
    jmp .merge
.scalar:
    call goldbach_segment_scalar
.merge:
    call seg_records
    call count_segment_primes
    add [r15 + HDR_PC], rax
    inc r13
    jmp .seg
.store:
    mov rcx, [r15 + HDR_SLOT]
    mov rax, [r15 + HDR_FBC]
    mov [rcx + SLOT_FBC], rax
    mov rax, [r15 + HDR_VIO]
    mov [rcx + SLOT_VIO], rax
    mov rax, [r15 + HDR_PC]
    mov [rcx + SLOT_PC], rax
    mov rax, [r15 + HDR_NREC]
    mov [rcx + SLOT_NREC], rax
    mov rax, [r15 + HDR_NFB]
    mov [rcx + SLOT_NFB], rax
    lea rax, [rbx+1]
    mov [rcx + SLOT_DONE], rax           ; done marker last (x86 stores are ordered)
    mov eax, 1
    jmp .ret
.mismatch:
    lea rbx, [r15 + HDR_LOGSB]
    mov rdi, rbx
    mov qword [rdi+8], 0
    lea rsi, [s_check_fail]
    call sb_putz
    mov rdi, rbx
    mov rsi, [r15 + HDR_SEGBASE]
    add rsi, PMAX
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_nl]
    call sb_putz
    mov rdi, rbx
    lea rsi, [s_check_v]
    call sb_putz
    mov rdi, rbx
    mov rsi, [r15 + HDR_CHKD]
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_check_n]
    call sb_putz
    mov rdi, rbx
    mov rsi, [r15 + HDR_CHKN]
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_nl]
    call sb_putz
    mov rdi, rbx
    lea rsi, [s_check_s]
    call sb_putz
    mov rdi, rbx
    mov rsi, [r15 + HDR_SEGMAXD]
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_check_n]
    call sb_putz
    mov rdi, rbx
    mov rsi, [r15 + HDR_SEGMAXN]
    call sb_putu
    mov rdi, rbx
    lea rsi, [s_nl]
    call sb_putz
    mov rdi, rbx
    mov rsi, [g_hstdout]
    call sb_flush
    mov edi, 3
    call os_exit
.ret:
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; try_advance(): merge completed chunks in order of N, update the verified
; frontier, write records, checkpoint every CP_SECS seconds.
; ---------------------------------------------------------------------------
try_advance:
    push rbx
    push r12
    push r13
    lea rdi, [g_lock]
    call lock_acquire
    xor r12d, r12d                       ; "advanced" flag
.loop:
    mov rbx, [g_frontier]
    mov eax, ebx
    and eax, RING-1
    shl eax, 13
    lea r13, [g_slots]
    add r13, rax
    lea rax, [rbx+1]
    cmp [r13 + SLOT_DONE], rax
    jne .end
    push r14
    xor r14d, r14d                       ; fast-path record candidates, in order of N
.rec:
    cmp r14, [r13 + SLOT_NREC]
    jae .rec_done
    mov rax, r14
    shl rax, 4
    mov rsi, [r13 + rax + SLOT_RECS + 8]
    cmp rsi, [g_max_depth]
    jbe .rec_next
    mov rdi, [r13 + rax + SLOT_RECS]
    call record_fast
.rec_next:
    inc r14
    jmp .rec
.rec_done:
    xor r14d, r14d                       ; fallback record candidates
.fbrec:
    cmp r14, [r13 + SLOT_NFB]
    jae .fbrec_done
    mov rax, r14
    shl rax, 4
    mov rsi, [r13 + rax + SLOT_FBRECS + 8]
    cmp rsi, [g_fb_max_depth]
    jbe .fbrec_next
    mov rdi, [r13 + rax + SLOT_FBRECS]
    call record_fb
.fbrec_next:
    inc r14
    jmp .fbrec
.fbrec_done:
    pop r14
    mov rax, [r13 + SLOT_FBC]
    add [g_fb_count], rax
    mov rax, [r13 + SLOT_VIO]
    add [g_violations], rax
    mov rax, [r13 + SLOT_PC]
    add [g_prime_count], rax
    mov qword [r13 + SLOT_DONE], 0
    lea rax, [rbx+1]
    mov [g_frontier], rax
    mov rdx, CHUNK
    mul rdx
    add rax, [g_N0]
    sub rax, 2
    mov [g_verified], rax
    mov r12d, 1
    mov rcx, [g_until]
    test rcx, rcx
    jz .loop
    cmp rax, rcx
    jb .loop
    mov byte [g_stop], 1
    jmp .loop
.end:
    test r12d, r12d
    jz .unlock
    call os_time_ms
    sub rax, [g_last_cp_ms]
    cmp rax, CP_SECS*1000
    jb .unlock
    call checkpoint_write
.unlock:
    lea rdi, [g_lock]
    call lock_release
    pop r13
    pop r12
    pop rbx
    ret

; cp_line(rdi=key, rsi=value, rdx=suffix or 0): "key value[suffix]\n\n" into g_msb
cp_line:
    push rbx
    push r12
    mov rbx, rsi
    mov r12, rdx
    mov rsi, rdi
    lea rdi, [g_msb]
    call sb_putz
    lea rdi, [g_msb]
    mov rsi, rbx
    call sb_putu
    test r12, r12
    jz .nosuf
    lea rdi, [g_msb]
    mov rsi, r12
    call sb_putz
.nosuf:
    lea rdi, [g_msb]
    lea rsi, [s_rec_end]
    call sb_putz
    pop r12
    pop rbx
    ret

; checkpoint_write(): atomically replace checkpoint.txt (write tmp, rename)
checkpoint_write:
    push rbx
    lea rdi, [g_msb]
    mov qword [rdi+8], 0
    lea rdi, [k_ver]
    mov rsi, [g_verified]
    xor edx, edx
    call cp_line
    lea rdi, [k_fail]
    mov rsi, [g_violations]
    xor edx, edx
    call cp_line
    lea rdi, [k_fbc]
    mov rsi, [g_fb_count]
    xor edx, edx
    call cp_line
    lea rdi, [k_fbn]
    mov rsi, [g_fb_max_N]
    xor edx, edx
    call cp_line
    lea rdi, [k_fbd]
    mov rsi, [g_fb_max_depth]
    lea rdx, [s_checks]
    call cp_line
    lea rdi, [k_maxn]
    mov rsi, [g_max_N]
    xor edx, edx
    call cp_line
    lea rdi, [k_maxd]
    mov rsi, [g_max_depth]
    lea rdx, [s_checks]
    call cp_line
    lea rdi, [k_pc]
    mov rsi, [g_prime_count]
    xor edx, edx
    call cp_line
    lea rdi, [g_msb]
    lea rsi, [k_ts]
    call sb_putz
    lea rdi, [g_msb]
    call sb_put_timestamp
    lea rdi, [g_msb]
    mov esi, 10
    call sb_putc
    lea rdi, [f_cp_tmp]
    mov esi, 2                           ; create / truncate
    call os_open
    test rax, rax
    js .fail
    mov rbx, rax
    lea rdi, [g_msb]
    mov rsi, rbx
    call sb_flush
    mov rdi, rbx
    call os_close
    lea rdi, [f_cp_tmp]
    lea rsi, [f_checkpoint]
    call os_rename
    call os_time_ms
    mov [g_last_cp_ms], rax
    pop rbx
    ret
.fail:
    lea rdi, [s_cp_err]
    call puts_out
    pop rbx
    ret

; checkpoint_read(): load the globals named in cp_table from checkpoint.txt
checkpoint_read:
    push rbx
    push r12
    push r13
    lea rdi, [f_checkpoint]
    xor esi, esi                         ; read
    call os_open
    test rax, rax
    js .ret
    mov r12, rax
    mov rdi, r12
    lea rsi, [g_cpbuf]
    mov edx, 2047
    call os_read
    mov r13, rax
    mov rdi, r12
    call os_close
    test r13, r13
    jle .ret
    lea rbx, [g_cpbuf]
    mov byte [rbx + r13], 0
.line:
    cmp byte [rbx], 0
    je .ret
    lea r12, [cp_table]
.key:
    mov rsi, [r12]
    test rsi, rsi
    jz .skip
    mov rdi, rbx
    call strprefix
    test eax, eax
    jnz .match
    add r12, 16
    jmp .key
.match:
    lea rdi, [rbx + rdx]
    call parse_u64
    mov rcx, [r12+8]
    mov [rcx], rax
.skip:
    movzx eax, byte [rbx]
    test eax, eax
    jz .ret
    inc rbx
    cmp al, 10
    jne .skip
    jmp .line
.ret:
    pop r13
    pop r12
    pop rbx
    ret

; st_line(rdi=label, rsi=value): "label value\n" into g_outsb
st_line:
    push rbx
    mov rbx, rsi
    mov rsi, rdi
    lea rdi, [g_outsb]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, rbx
    call sb_putu
    lea rdi, [g_outsb]
    mov esi, 10
    call sb_putc
    pop rbx
    ret

; status_print(): the "status" command
status_print:
    lea rdi, [g_outsb]
    mov qword [rdi+8], 0
    lea rdi, [s_st_ver]
    mov rsi, [g_verified]
    call st_line
    lea rdi, [s_st_pi]
    mov rsi, [g_prime_count]
    call st_line
    call os_time_ms
    sub rax, [g_t0_ms]
    mov rcx, rax
    test rcx, rcx
    jnz .t_ok
    mov ecx, 1
.t_ok:
    mov rax, [g_verified]
    sub rax, [g_run_start]
    xor edx, edx
    mov r8, rcx
    mov rcx, 1000
    mul rcx
    div r8
    mov rsi, rax
    lea rdi, [g_outsb]
    push rsi
    lea rsi, [s_st_rate]
    call sb_putz
    pop rsi
    lea rdi, [g_outsb]
    call sb_putu
    lea rdi, [g_outsb]
    lea rsi, [s_st_rate2]
    call sb_putz
    lea rdi, [s_st_fa]
    mov rsi, [g_fb_count]
    call st_line
    lea rdi, [s_st_lfn]
    mov rsi, [g_fb_max_N]
    call st_line
    lea rdi, [s_st_mfd]
    mov rsi, [g_fb_max_depth]
    call st_line
    lea rdi, [s_st_mfsd]
    mov rsi, [g_max_depth]
    call st_line
    lea rdi, [s_st_mfsn]
    mov rsi, [g_max_N]
    call st_line
    mov rsi, [g_violations]
    test rsi, rsi
    jz .novio
    lea rdi, [s_st_vio]
    call st_line
    jmp .flush
.novio:
    lea rdi, [g_outsb]
    lea rsi, [s_st_none]
    call sb_putz
.flush:
    lea rdi, [g_outsb]
    mov rsi, [g_hstdout]
    call sb_flush
    ret

; process_cmd(rdi = start, rsi = end: a line inside g_linebuf) -> eax = 1 to stop
process_cmd:
    lea r8, [g_linebuf]
    lea r9, [g_cmdbuf]
.rstrip:
    cmp rsi, rdi
    jbe .lstrip
    movzx eax, byte [r8 + rsi - 1]
    cmp al, ' '
    ja .lstrip
    dec rsi
    jmp .rstrip
.lstrip:
    cmp rdi, rsi
    jae .copy
    movzx eax, byte [r8 + rdi]
    cmp al, ' '
    ja .copy
    inc rdi
    jmp .lstrip
.copy:                                   ; lower-cased copy into g_cmdbuf
    xor ecx, ecx
.cp:
    cmp rdi, rsi
    jae .term
    cmp ecx, 63
    jae .term
    movzx eax, byte [r8 + rdi]
    cmp al, 'A'
    jb .store
    cmp al, 'Z'
    ja .store
    add al, 32
.store:
    mov [r9 + rcx], al
    inc ecx
    inc rdi
    jmp .cp
.term:
    mov byte [r9 + rcx], 0
    test ecx, ecx
    jz .none
    lea rdi, [g_cmdbuf]
    lea rsi, [c_status]
    call streq
    test eax, eax
    jz .not_status
    call status_print
    jmp .none
.not_status:
    lea rdi, [g_cmdbuf]
    lea rsi, [c_stop]
    call streq
    test eax, eax
    jnz .stop
    lea rdi, [g_cmdbuf]
    lea rsi, [c_quit]
    call streq
    test eax, eax
    jz .unknown
    lea rdi, [s_forcequit]
    call puts_out
    xor edi, edi
    call os_exit
.unknown:
    lea rdi, [s_cmds]
    call puts_out
.none:
    xor eax, eax
    ret
.stop:
    mov eax, 1
    ret

; cmd_loop(): read commands from stdin until stop/EOF/signal.  A read may
; return several lines (piped input) or one; every complete line is handled.
cmd_loop:
    push rbx
    push r12
    push r13
.prompt:
    lea rdi, [s_prompt]
    call puts_out
.read:
    mov rdi, [g_hstdin]
    lea rsi, [g_linebuf]
    mov edx, 255
    call os_read
    cmp rax, -1
    je .interrupted
    test rax, rax
    jle .eof
    mov r12, rax                         ; bytes read
    xor r13d, r13d                       ; start of the current line
.line:
    mov rbx, r13
.scan:
    cmp rbx, r12
    jae .have
    lea rax, [g_linebuf]
    cmp byte [rax + rbx], 10
    je .have
    inc rbx
    jmp .scan
.have:
    mov rdi, r13
    mov rsi, rbx
    call process_cmd
    test eax, eax
    jnz .ret
    lea r13, [rbx+1]
    cmp r13, r12
    jb .line
    jmp .prompt
.interrupted:
    cmp byte [g_stop], 0
    jne .ret
    cmp qword [g_active], 0
    je .ret
    jmp .read
.eof:                                    ; stdin closed: keep running until stop/limit/until
    cmp byte [g_stop], 0
    jne .ret
    cmp qword [g_active], 0
    je .ret
    mov edi, 100
    call os_sleep_ms
    jmp .eof
.ret:
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; Threads and signals
; ---------------------------------------------------------------------------
%ifdef WIN64
worker_entry_win:                        ; CreateThread entry: rcx = context
    mov r15, rcx
    jmp worker_entry
%else
worker_entry_linux:                      ; clone child: context pointer at the stack top
    mov r15, [rsp]
    and rsp, -16
    jmp worker_entry
%endif
worker_entry:
.loop:
    cmp byte [g_stop], 0
    jne .exit
    mov eax, 1
    lock xadd [g_next_chunk], rax
    mov rbx, rax
    mov rax, CHUNK                       ; first number of the chunk; the chunk must end below 2^64
    mul rbx
    test rdx, rdx
    jnz .end64
    add rax, [g_N0]
    jc .end64
    add rax, CHUNK
    jc .end64
    sub rax, CHUNK
    mov rcx, [g_until]                   ; --until: never start a chunk beyond it
    test rcx, rcx
    jz .wait
    cmp rax, rcx
    ja .exit
.wait:                                   ; stay within RING chunks of the frontier
    mov rax, [g_frontier]
    mov rcx, rbx
    sub rcx, rax
    cmp rcx, RING
    jb .go
    cmp byte [g_stop], 0
    jne .exit
    mov edi, 1
    call os_sleep_ms
    jmp .wait
.go:
    mov rdi, rbx
    call process_chunk
    test eax, eax
    jz .exit
    call try_advance
    jmp .loop
.end64:
    mov qword [g_end64], 1
    mov byte [g_stop], 1
.exit:
    cmp qword [g_log_mode], 0
    je .noflush
    lea rdi, [r15 + HDR_LOGSB]
    mov rsi, [g_fd_log]
    call sb_flush
.noflush:
    mov rax, -1
    lock xadd [g_active], rax
    cmp rax, 1
    jne .bye
    call os_wake_main                    ; last worker out: wake main's blocking read
.bye:
    call os_thread_exit

; ===========================================================================
; OS layer.  Everything above is OS-independent; these are the only places
; that talk to the operating system.
;   os_init, os_write(h,buf,len), os_read(h,buf,len) -> n | 0 eof | -1 interrupted,
;   os_open(path, mode 0 read / 1 append / 2 truncate) -> handle | -1, os_close(h),
;   os_rename(a,b), os_alloc(size), os_commit(ptr,size), os_thread_start(ctx),
;   os_thread_join(ctx), os_thread_exit, os_wake_main, os_exit(code), os_cpu_count,
;   os_time_ms, os_utc_secs, os_sleep_ms(ms), os_install_handlers,
;   os_block_signals / os_unblock_signals.
; ===========================================================================
%ifdef WIN64
; ---- Windows: kernel32 only, imported through the table at the end of the file
%macro WINFRAME 0                        ; 16-byte aligned frame with shadow space + 8 slots
    push rbp
    mov rbp, rsp
    and rsp, -16
    sub rsp, 96
%endmacro
%macro WINRET 0
    mov rsp, rbp
    pop rbp
    ret
%endmacro

os_init:                                 ; console handles, main-thread handle, argv block
    WINFRAME
    mov ecx, -10
    call [GetStdHandle]
    mov [g_hstdin], rax
    mov ecx, -11
    call [GetStdHandle]
    mov [g_hstdout], rax
    call [GetCurrentProcess]
    mov [rsp+56], rax
    call [GetCurrentThread]
    mov rdx, rax
    mov rcx, [rsp+56]
    mov r8, [rsp+56]
    lea r9, [g_main_thread]
    mov qword [rsp+32], 0
    mov qword [rsp+40], 0
    mov qword [rsp+48], 2                ; DUPLICATE_SAME_ACCESS
    call [DuplicateHandle]
    call [GetCommandLineA]
    lea rdx, [g_cmdline]
    xor ecx, ecx
.copy:
    mov r8b, [rax + rcx]
    mov [rdx + rcx], r8b
    test r8b, r8b
    jz .copied
    inc ecx
    cmp ecx, 4095
    jb .copy
    mov byte [rdx + rcx], 0
.copied:
    lea r8, [g_argblock]
    xor r9d, r9d                         ; argc
    mov rcx, rdx
.tok:
    movzx eax, byte [rcx]
    test eax, eax
    jz .tokdone
    cmp al, ' '
    je .skip
    cmp al, 9
    je .skip
    cmp al, '"'
    jne .plain
    inc rcx                              ; quoted token
    mov [r8 + 8 + r9*8], rcx
.q:
    movzx eax, byte [rcx]
    test eax, eax
    jz .tokend
    cmp al, '"'
    je .qend
    inc rcx
    jmp .q
.qend:
    mov byte [rcx], 0
    inc rcx
    jmp .tokend
.plain:
    mov [r8 + 8 + r9*8], rcx
.p:
    movzx eax, byte [rcx]
    test eax, eax
    jz .tokend
    cmp al, ' '
    je .pend
    cmp al, 9
    je .pend
    inc rcx
    jmp .p
.pend:
    mov byte [rcx], 0
    inc rcx
.tokend:
    inc r9
    cmp r9, 62
    jb .tok
    jmp .tokdone
.skip:
    inc rcx
    jmp .tok
.tokdone:
    mov [r8], r9
    WINRET

os_write:                                ; (rdi=handle, rsi=buf, rdx=len) -> rax bytes written
    WINFRAME
    mov rcx, rdi
    mov r8, rdx
    mov rdx, rsi
    cmp r8, 0x40000000
    jbe .len_ok
    mov r8d, 0x40000000
.len_ok:
    lea r9, [rsp+40]
    mov qword [rsp+32], 0
    mov qword [rsp+40], 0
    call [WriteFile]
    test eax, eax
    jz .fail
    mov eax, [rsp+40]
    WINRET
.fail:
    mov rax, -1
    WINRET

os_read:                                 ; (rdi=handle, rsi=buf, rdx=len)
    WINFRAME
    mov rcx, rdi
    mov r8d, edx
    mov rdx, rsi
    lea r9, [rsp+40]
    mov qword [rsp+32], 0
    mov qword [rsp+40], 0
    call [ReadFile]
    test eax, eax
    jz .err
    mov eax, [rsp+40]
    WINRET
.err:
    call [GetLastError]
    cmp eax, 995                         ; ERROR_OPERATION_ABORTED: Ctrl-C or CancelSynchronousIo
    mov rax, -1
    je .done
    xor eax, eax                         ; anything else: treat as end of input
.done:
    WINRET

os_open:                                 ; (rdi=path, esi=mode) -> handle or -1
    WINFRAME
    mov rcx, rdi
    mov edx, 0x80000000                  ; GENERIC_READ
    mov r8d, 3                           ; FILE_SHARE_READ | FILE_SHARE_WRITE
    mov qword [rsp+32], 3                ; OPEN_EXISTING
    test esi, esi
    jz .call
    mov edx, 4                           ; FILE_APPEND_DATA
    mov r8d, 1                           ; FILE_SHARE_READ
    mov qword [rsp+32], 4                ; OPEN_ALWAYS
    cmp esi, 1
    je .call
    mov edx, 0x40000000                  ; GENERIC_WRITE
    mov qword [rsp+32], 2                ; CREATE_ALWAYS
.call:
    xor r9d, r9d
    mov qword [rsp+40], 0x80             ; FILE_ATTRIBUTE_NORMAL
    mov qword [rsp+48], 0
    call [CreateFileA]                   ; INVALID_HANDLE_VALUE is already -1
    WINRET

os_close:
    WINFRAME
    mov rcx, rdi
    call [CloseHandle]
    WINRET

os_rename:                               ; (rdi=from, rsi=to), replacing the target
    WINFRAME
    mov rcx, rdi
    mov rdx, rsi
    mov r8d, 9                           ; MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH
    call [MoveFileExA]
    WINRET

os_alloc:                                ; reserve address space; os_commit makes parts usable
    WINFRAME
    xor ecx, ecx
    mov rdx, rdi
    mov r8d, 0x2000                      ; MEM_RESERVE
    mov r9d, 4                           ; PAGE_READWRITE
    call [VirtualAlloc]
    test rax, rax
    jz .fail
    WINRET
.fail:
    mov edi, 4
    call os_exit

os_commit:                               ; (rdi=ptr, rsi=size)
    WINFRAME
    mov rcx, rdi
    mov rdx, rsi
    mov r8d, 0x1000                      ; MEM_COMMIT
    mov r9d, 4
    call [VirtualAlloc]
    test rax, rax
    jz .fail
    WINRET
.fail:
    mov edi, 4
    call os_exit

os_thread_start:                         ; (rdi=ctx): handle kept in HDR_TID
    WINFRAME
    mov [rsp+56], rdi
    xor ecx, ecx
    xor edx, edx
    lea r8, [worker_entry_win]
    mov r9, rdi
    mov qword [rsp+32], 0
    mov qword [rsp+40], 0
    call [CreateThread]
    test rax, rax
    jz .fail
    mov rcx, [rsp+56]
    mov [rcx + HDR_TID], rax
    WINRET
.fail:
    mov edi, 5
    call os_exit

os_thread_join:                          ; (rdi=ctx)
    WINFRAME
    mov [rsp+56], rdi
    mov rcx, [rdi + HDR_TID]
    mov edx, -1                          ; INFINITE
    call [WaitForSingleObject]
    mov rdi, [rsp+56]
    mov rcx, [rdi + HDR_TID]
    call [CloseHandle]
    WINRET

os_thread_exit:
    WINFRAME
    xor ecx, ecx
    call [ExitThread]

os_wake_main:                            ; break the main thread out of its console read
    WINFRAME
    mov rcx, [g_main_thread]
    call [CancelSynchronousIo]
    WINRET

os_exit:                                 ; (edi=code)
    WINFRAME
    mov ecx, edi
    call [ExitProcess]

os_cpu_count:
    WINFRAME
    lea rcx, [rsp+32]                    ; SYSTEM_INFO (48 bytes)
    call [GetSystemInfo]
    mov eax, [rsp+32+32]                 ; dwNumberOfProcessors
    test eax, eax
    jnz .ok
    mov eax, 1
.ok:
    WINRET

os_time_ms:
    WINFRAME
    call [GetTickCount64]
    WINRET

os_utc_secs:                             ; seconds since 1970-01-01 UTC
    WINFRAME
    lea rcx, [rsp+40]
    call [GetSystemTimeAsFileTime]
    mov rax, [rsp+40]
    mov rcx, 116444736000000000          ; 1601 -> 1970 in 100 ns units
    sub rax, rcx
    xor edx, edx
    mov rcx, 10000000
    div rcx
    WINRET

os_sleep_ms:                             ; (edi=ms)
    WINFRAME
    mov ecx, edi
    call [Sleep]
    WINRET

os_install_handlers:                     ; Ctrl-C / close -> graceful stop
    WINFRAME
    lea rcx, [ctrl_handler]
    mov edx, 1
    call [SetConsoleCtrlHandler]
    WINRET

os_block_signals:
os_unblock_signals:
    ret

ctrl_handler:                            ; BOOL WINAPI (DWORD type): runs on its own thread
    sub rsp, 40
    mov byte [g_stop], 1
    mov rcx, [g_main_thread]
    call [CancelSynchronousIo]
    add rsp, 40
    mov eax, 1
    ret

%else
; ---- Linux: raw system calls --------------------------------------------------
os_init:
    mov qword [g_hstdin], 0
    mov qword [g_hstdout], 1
    ret

os_write:                                ; (rdi=fd, rsi=buf, rdx=len) -> rax
    mov eax, SYS_write
    syscall
    cmp rax, -EINTR
    je os_write
    ret

os_read:                                 ; (rdi=fd, rsi=buf, rdx=len)
    mov eax, SYS_read
    syscall
    cmp rax, -EINTR
    je .intr
    test rax, rax
    jns .ok
    xor eax, eax
.ok:
    ret
.intr:
    mov rax, -1
    ret

os_open:                                 ; (rdi=path, esi=mode) -> fd or -1
    mov eax, O_RDONLY
    test esi, esi
    jz .go
    mov eax, O_WRONLY|O_CREAT|O_APPEND
    cmp esi, 1
    je .go
    mov eax, O_WRONLY|O_CREAT|O_TRUNC
.go:
    mov esi, eax
    mov eax, SYS_open
    mov edx, 0644o
    syscall
    test rax, rax
    jns .ok
    mov rax, -1
.ok:
    ret

os_close:
    mov eax, SYS_close
    syscall
    ret

os_rename:
    mov eax, SYS_rename
    syscall
    ret

os_alloc:                                ; mmap with MAP_NORESERVE: pages appear when touched
    mov rsi, rdi
    mov eax, SYS_mmap
    xor edi, edi
    mov edx, PROT_RW
    mov r10d, MAP_PRIV_ANON
    mov r8, -1
    xor r9d, r9d
    syscall
    cmp rax, -4096
    ja .fail
    ret
.fail:
    mov edi, 4
    call os_exit

os_commit:                               ; nothing to do: see os_alloc
    ret

os_thread_start:                         ; (rdi=ctx): clone with the stack inside the context
    lea rsi, [rdi + CTX_SIZE - 64]       ; child stack top; the context pointer sits there
    mov [rsi], rdi
    lea rdx, [rdi + HDR_TID]
    lea r10, [rdi + HDR_TID]
    xor r8d, r8d
    mov edi, CLONE_FLAGS
    mov eax, SYS_clone
    syscall
    test rax, rax
    jz worker_entry_linux                ; child
    js .fail
    ret
.fail:
    mov edi, 5
    call os_exit

os_thread_join:                          ; (rdi=ctx): the kernel clears HDR_TID on exit
.wait:
    mov edx, [rdi + HDR_TID]
    test edx, edx
    jz .done
    push rdi
    lea rdi, [rdi + HDR_TID]
    mov esi, FUTEX_WAIT
    xor r10d, r10d
    mov eax, SYS_futex
    syscall
    pop rdi
    jmp .wait
.done:
    ret

os_thread_exit:
    mov eax, SYS_exit
    xor edi, edi
    syscall

os_wake_main:                            ; SIGUSR1 is only unblocked in the main thread
    mov eax, SYS_getpid
    syscall
    mov edi, eax
    mov esi, SIGUSR1
    mov eax, SYS_kill
    syscall
    ret

os_exit:                                 ; (edi=code)
    mov eax, SYS_exit_group
    syscall

os_cpu_count:                            ; CPUs in this process's affinity mask (>= 1)
    mov eax, SYS_sched_getaffinity
    xor edi, edi
    mov esi, 128
    lea rdx, [g_cpumask]
    syscall
    test rax, rax
    jle .one
    lea rsi, [g_cpumask]
    mov rcx, rax
    xor eax, eax
.loop:
    test rcx, rcx
    jz .done
    movzx edx, byte [rsi + rcx - 1]
.bits:
    test edx, edx
    jz .next
    lea r8d, [rdx-1]
    and edx, r8d
    inc rax
    jmp .bits
.next:
    dec rcx
    jmp .loop
.done:
    test rax, rax
    jnz .ret
.one:
    mov eax, 1
.ret:
    ret

os_time_ms:                              ; CLOCK_MONOTONIC in milliseconds
    sub rsp, 16
    mov eax, SYS_clock_gettime
    mov edi, 1
    mov rsi, rsp
    syscall
    mov rax, [rsp]
    imul rax, rax, 1000
    mov rcx, [rsp+8]
    push rax
    mov rax, rcx
    xor edx, edx
    mov rcx, 1000000
    div rcx
    pop rcx
    add rax, rcx
    add rsp, 16
    ret

os_utc_secs:                             ; CLOCK_REALTIME seconds
    sub rsp, 16
    mov eax, SYS_clock_gettime
    xor edi, edi
    mov rsi, rsp
    syscall
    mov rax, [rsp]
    add rsp, 16
    ret

os_sleep_ms:                             ; (edi=ms)
    sub rsp, 16
    mov eax, edi
    xor edx, edx
    mov ecx, 1000
    div rcx
    mov [rsp], rax
    imul rdx, rdx, 1000000
    mov [rsp+8], rdx
    mov eax, SYS_nanosleep
    mov rdi, rsp
    xor esi, esi
    syscall
    add rsp, 16
    ret

os_install_handlers:                     ; SIGINT / SIGTERM -> stop; SIGUSR1 just interrupts read
    mov edi, SIGINT
    lea rsi, [sig_stop]
    call sigaction_set
    mov edi, SIGTERM
    lea rsi, [sig_stop]
    call sigaction_set
    mov edi, SIGUSR1
    lea rsi, [sig_noop]
    jmp sigaction_set

os_block_signals:                        ; workers inherit the mask -> signals reach main only
    xor edi, edi
    jmp sigmask_set
os_unblock_signals:
    mov edi, 1
    jmp sigmask_set

sig_stop:
    mov byte [g_stop], 1
    ret
sig_noop:
    ret
sig_restorer:
    mov eax, SYS_rt_sigreturn
    syscall

; sigaction_set(edi=signal, rsi=handler)
sigaction_set:
    mov [g_sigact], rsi
    mov qword [g_sigact+8], SA_RESTORER
    lea rax, [sig_restorer]
    mov [g_sigact+16], rax
    mov qword [g_sigact+24], 0
    mov eax, SYS_rt_sigaction
    lea rsi, [g_sigact]
    xor edx, edx
    mov r10d, 8
    syscall
    ret

; sigmask_set(edi = 0 block / 1 unblock) for SIGINT, SIGTERM, SIGUSR1
sigmask_set:
    mov qword [g_sigset], (1 << (SIGINT-1)) | (1 << (SIGTERM-1)) | (1 << (SIGUSR1-1))
    mov eax, SYS_rt_sigprocmask
    lea rsi, [g_sigset]
    xor edx, edx
    mov r10d, 8
    syscall
    ret
%endif

; cpu_detect(): pick the AVX2 or the plain code path, and hardware POPCNT
; when available.  Everything else is baseline x86-64.
cpu_detect:
    push rbx
    mov eax, 1
    xor ecx, ecx
    cpuid
    mov edx, ecx
    shr edx, 23
    and edx, 1
    mov [g_have_popcnt], dl
    and ecx, (1<<27)|(1<<28)             ; OSXSAVE and AVX
    cmp ecx, (1<<27)|(1<<28)
    jne .noavx2
    xor ecx, ecx
    xgetbv
    and eax, 6                           ; XMM and YMM state enabled by the OS
    cmp eax, 6
    jne .noavx2
    mov eax, 7
    xor ecx, ecx
    cpuid
    test ebx, 1<<5                       ; AVX2
    jz .noavx2
    mov byte [g_have_avx2], 1
.noavx2:
    call cpu_select
    pop rbx
    ret

; cpu_select(): set the function pointer(s) from the feature flags
cpu_select:
    lea rax, [vec_pass_scalar]
    cmp byte [g_have_avx2], 0
    je .set
    lea rax, [vec_pass_avx2]
.set:
    mov [g_vec_pass], rax
    ret

; spawn_workers(): one context + thread per worker
spawn_workers:
    push rbx
    push r12
    xor r12d, r12d
.next:
    cmp r12, [g_nthreads]
    jae .done
    mov rdi, CTX_SIZE
    call os_alloc
    mov rbx, rax
    mov rdi, rbx                         ; bitmaps, header, unresolved map
    mov esi, CTX_NEXTJ
    call os_commit
    lea rdi, [rbx + CTX_LOGBUF]          ; log buffer + first-N table
    mov esi, CTX_STACK - CTX_LOGBUF
    call os_commit
    lea rax, [g_ctx]
    mov [rax + r12*8], rbx
    mov [rbx + HDR_IDX], r12
    lea rdi, [rbx + HDR_LOGSB]
    lea rsi, [rbx + CTX_LOGBUF]
    mov edx, LOGBUF_SIZE
    call sb_init
    mov rdi, rbx
    call os_thread_start
    inc r12
    jmp .next
.done:
    pop r12
    pop rbx
    ret

; join_workers(): wait for every worker thread to finish
join_workers:
    push rbx
    push r12
    xor r12d, r12d
.next:
    cmp r12, [g_nthreads]
    jae .done
    lea rbx, [g_ctx]
    mov rbx, [rbx + r12*8]
    mov rdi, rbx
    call os_thread_join
    inc r12
    jmp .next
.done:
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; main
; ---------------------------------------------------------------------------
usage_exit:
    lea rdi, [s_usage]
    call puts_out
    mov edi, 1
    call os_exit

; opt_value(): rax = numeric value of argv[r12+1], advancing r12 (rbp = &argc)
opt_value:
    inc r12
    cmp r12, [rbp]
    jae usage_exit
    mov rdi, [rbp + 8 + r12*8]
    call parse_u64
    ret

_start:
%ifndef WIN64
    mov rbp, rsp                         ; argc at [rbp], argv pointers follow
%endif
    call os_init
%ifdef WIN64
    lea rbp, [g_argblock]                ; same layout, built from GetCommandLineA
%endif
    call cpu_detect
    lea rdi, [g_outsb]
    lea rsi, [g_outbuf]
    mov edx, 4096
    call sb_init
    lea rdi, [g_msb]
    lea rsi, [g_mbuf]
    mov edx, 4096
    call sb_init
    lea rdi, [g_vsb]
    lea rsi, [g_vbuf]
    mov edx, 512
    call sb_init
    lea rdi, [g_logsb]
    lea rsi, [g_logbuf]
    mov edx, LOGBUF_SIZE
    call sb_init
    call os_cpu_count
    mov [g_nthreads], rax

    mov r12d, 1                          ; ---- arguments ----
.arg:
    cmp r12, [rbp]
    jae .args_done
    mov rbx, [rbp + 8 + r12*8]
    mov rdi, rbx
    lea rsi, [o_threads]
    call streq
    test eax, eax
    jz .a1
    call opt_value
    mov [g_nthreads], rax
    jmp .anext
.a1:
    mov rdi, rbx
    lea rsi, [o_start]
    call streq
    test eax, eax
    jz .a2
    call opt_value
    mov [g_start_opt], rax
    jmp .anext
.a2:
    mov rdi, rbx
    lea rsi, [o_until]
    call streq
    test eax, eax
    jz .a3
    call opt_value
    mov [g_until], rax
    jmp .anext
.a3:
    mov rdi, rbx
    lea rsi, [o_log]
    call streq
    test eax, eax
    jz .a4
    mov qword [g_log_mode], 1
    jmp .anext
.a4:
    mov rdi, rbx
    lea rsi, [o_check]
    call streq
    test eax, eax
    jz .a5
    mov qword [g_check_mode], 1
    jmp .anext
.a5:
    mov rdi, rbx
    lea rsi, [o_nfast]
    call streq
    test eax, eax
    jz .a6
    call opt_value
    mov [g_nfast_opt], rax
    jmp .anext
.a6:
    mov rdi, rbx
    lea rsi, [o_baseline]
    call streq
    test eax, eax
    jz .a7
    mov byte [g_have_avx2], 0
    mov byte [g_have_popcnt], 0
    call cpu_select
    jmp .anext
.a7:
    mov rdi, rbx
    lea rsi, [o_help]
    call streq
    test eax, eax
    jnz usage_exit
    lea rdi, [s_badarg]
    call puts_out
    mov rdi, rbx
    call puts_out
    lea rdi, [s_nl]
    call puts_out
    jmp usage_exit
.anext:
    inc r12
    jmp .arg
.args_done:
    cmp qword [g_log_mode], 0
    je .thr_ok
    mov qword [g_nthreads], 1            ; --log needs chunks in order: one worker
.thr_ok:
    mov rax, [g_nthreads]
    test rax, rax
    jnz .thr_min
    mov qword [g_nthreads], 1
.thr_min:
    cmp qword [g_nthreads], MAX_THREADS
    jbe .thr_max
    mov qword [g_nthreads], MAX_THREADS
.thr_max:

    lea rdi, [s_banner]                  ; ---- banner + base primes ----
    call puts_out
    lea rdi, [g_outsb]
    lea rsi, [s_using]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_nthreads]
    call sb_putu
    lea rdi, [g_outsb]
    lea rsi, [s_workers]
    call sb_putz
    lea rdi, [g_outsb]
    lea rsi, [s_cpu_plain]
    cmp byte [g_have_avx2], 0
    je .cpu1
    lea rsi, [s_cpu_avx2]
.cpu1:
    call sb_putz
    cmp byte [g_have_popcnt], 0
    je .cpu2
    lea rdi, [g_outsb]
    lea rsi, [s_cpu_popcnt]
    call sb_putz
.cpu2:
    lea rdi, [g_outsb]
    lea rsi, [s_nl]
    call sb_putz
    lea rdi, [g_outsb]
    lea rsi, [s_building]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, BASE_INIT
    call sb_putu
    lea rdi, [g_outsb]
    mov rsi, [g_hstdout]
    call sb_flush
    mov rdi, BASE_BYTES_MAX
    call os_alloc
    mov [g_base_bits], rax
    mov rdi, rax
    mov esi, BASE_INIT/16
    call os_commit
    mov rdi, MAX_BASE*4
    call os_alloc
    mov [g_base_primes], rax
    mov rdi, rax
    mov esi, BASE_INIT/4
    call os_commit
    call build_base
    lea rdi, [g_outsb]
    lea rsi, [s_builddone]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_n_base]
    inc rsi                              ; + the prime 2
    call sb_putu
    lea rdi, [g_outsb]
    lea rsi, [s_primes_nl]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_hstdout]
    call sb_flush

    mov rax, [g_start_opt]               ; ---- where to start ----
    test rax, rax
    jnz .explicit
    call checkpoint_read
    mov rax, [g_cp_verified]
    cmp rax, 4
    jb .fresh
    add rax, 2
    mov rbx, rax
    lea rdi, [g_outsb]
    lea rsi, [s_resume]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_cp_verified]
    call sb_putu
    jmp .start_known
.explicit:
    add rax, 1
    and rax, -2                          ; round up to even
    cmp rax, 4
    jae .exp_ok
    mov eax, 4
.exp_ok:
    mov rbx, rax
    jmp .fresh_msg
.fresh:
    mov ebx, 4
.fresh_msg:
    lea rdi, [g_outsb]
    lea rsi, [s_fresh]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, rbx
    call sb_putu
.start_known:
    lea rdi, [g_outsb]
    lea rsi, [s_nl]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_hstdout]
    call sb_flush

    lea rdi, [f_interesting]                  ; ---- output files ----
    mov esi, 1                           ; append
    call os_open
    test rax, rax
    js .open_fail
    mov [g_fd_int], rax
    lea rdi, [f_violations]
    mov esi, 1                           ; append
    call os_open
    test rax, rax
    js .open_fail
    mov [g_fd_vio], rax
    cmp qword [g_log_mode], 0
    je .files_ok
    lea rdi, [f_log]
    mov esi, 1                           ; append
    call os_open
    test rax, rax
    js .open_fail
    mov [g_fd_log], rax
.files_ok:
    lea rax, [rbx-2]
    mov [g_verified], rax
    cmp qword [g_prime_count], 0
    jne .pc_known
    cmp rax, [g_base_limit]
    jae .pc_known
    mov rdi, rax
    call pi_small
    mov [g_prime_count], rax
.pc_known:
    cmp rbx, SMALL_END                   ; ---- small numbers on the main thread ----
    jae .chunked
    mov rdi, rbx
    call small_path
    mov ebx, SMALL_END
    mov qword [g_verified], SMALL_END-2
    mov edi, SMALL_END-2
    call pi_small
    mov [g_prime_count], rax
    call checkpoint_write
.chunked:
    mov [g_N0], rbx
    mov rax, [g_verified]
    mov [g_run_start], rax
    call os_time_ms
    mov [g_t0_ms], rax
    mov [g_last_cp_ms], rax
    mov rax, [g_until]
    test rax, rax
    jz .go
    cmp [g_verified], rax
    jae .finish
.go:
    call os_install_handlers             ; Ctrl-C -> graceful stop
    call os_block_signals                ; workers inherit the mask (Linux)
    mov rax, [g_nthreads]
    mov [g_active], rax
    call spawn_workers
    call os_unblock_signals
    lea rdi, [s_running]
    call puts_out
    call cmd_loop
    mov byte [g_stop], 1
    lea rdi, [s_stopping]
    call puts_out
    call join_workers
    call try_advance
    call checkpoint_write
.finish:
    lea rdi, [g_outsb]
    mov qword [rdi+8], 0
    lea rsi, [s_sum1]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_verified]
    call sb_putu
    lea rdi, [g_outsb]
    lea rsi, [s_sum2]
    call sb_putz
    lea rdi, [g_outsb]
    mov rsi, [g_violations]
    call sb_putu
    lea rdi, [g_outsb]
    lea rsi, [s_sum3]
    call sb_putz
    cmp qword [g_end64], 0
    je .no_limit
    lea rdi, [g_outsb]
    lea rsi, [s_limit]
    call sb_putz
.no_limit:
    lea rdi, [g_outsb]
    mov rsi, [g_hstdout]
    call sb_flush
    xor edi, edi
    call os_exit
.open_fail:
    lea rdi, [s_open_err]
    call puts_out
    lea rdi, [s_nl]
    call puts_out
    mov edi, 6
    call os_exit

%ifdef WIN64
; ===========================================================================
; Windows import table (kernel32.dll), written by hand so that no import
; library is needed.  The loader fills the IAT entries that the code calls
; through, e.g. `call [WriteFile]`.
; ===========================================================================
%macro IMPORT 1
section .idata$4 data align=8
    dd hn_%1 wrt ..imagebase, 0
section .idata$5 data align=8
%1: dd hn_%1 wrt ..imagebase, 0
section .idata$6 data align=2
hn_%1: dw 0
    db %str(%1), 0
    times ($ - $$) & 1 db 0
%endmacro

section .idata$2 data align=4
    dd k32_ilt wrt ..imagebase, 0, 0, k32_name wrt ..imagebase, k32_iat wrt ..imagebase
section .idata$3 data align=4
    dd 0, 0, 0, 0, 0
section .idata$4 data align=8
k32_ilt:
section .idata$5 data align=8
k32_iat:
IMPORT GetStdHandle
IMPORT WriteFile
IMPORT ReadFile
IMPORT CreateFileA
IMPORT CloseHandle
IMPORT MoveFileExA
IMPORT VirtualAlloc
IMPORT CreateThread
IMPORT WaitForSingleObject
IMPORT ExitThread
IMPORT Sleep
IMPORT GetTickCount64
IMPORT GetSystemTimeAsFileTime
IMPORT GetSystemInfo
IMPORT ExitProcess
IMPORT SetConsoleCtrlHandler
IMPORT CancelSynchronousIo
IMPORT GetCurrentProcess
IMPORT GetCurrentThread
IMPORT DuplicateHandle
IMPORT GetCommandLineA
IMPORT GetLastError
section .idata$4 data align=8
    dq 0
section .idata$5 data align=8
    dq 0
section .idata$6 data align=2
k32_name: db "KERNEL32.dll", 0
%endif
