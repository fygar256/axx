; Brainfuck interpreter
; FreeBSD x86_64 / Linux x86_64
; Intel syntax (axx) -- マクロ層を使用
;
; build:
;   下の !set OS を "freebsd" / "linux" のどちらかにするだけで切り替わる。
;   (以前はソース中の .equ を手で書き換える必要があった)
;
;   python3 axx.py x86_64.axx bf.s -o bf.o --osabi FreeBSD && ld -o bf bf.o
;   python3 axx.py x86_64.axx bf.s -o bf.o --osabi Linux   && ld -o bf bf.o
;
;   展開結果だけを見たいとき:
;     python3 axx.py x86_64.axx bf.s -P
;
; ===== テープアクセスの方針 =====
; tape_a: .equ tape::abs32 と定義し、
; x86_64.axx の [!s\+r] パターンが 4バイト disp32 フィールドに
; R_X86_64_32 (絶対32bitアドレス) リロケーションを生成する。
;
; これにより [symbol+register] SIBアドレッシングが使用でき、
; r15 をテープインデックス (0オリジン) として扱える。
;
; レジスタ割り当て:
;   r12 = fd (ファイルオープン時のみ)
;   r13 = プログラム長 (バイト数)
;   r14 = 命令ポインタ (prog_buf インデックス)
;   r15 = テープインデックス (tape[r15] が現在セル)

; ===========================================================
; ビルド設定
; ===========================================================
!set OS        = "freebsd"      ; "freebsd" または "linux"
!set TAPE_SIZE = 65536
!set PROG_SIZE = 1048576

!echo "bf.s: OS=" + OS + " tape=" + str(TAPE_SIZE) + " prog=" + str(PROG_SIZE)

.global _start

; --- syscall番号 ---
!if OS == "freebsd" !then {
SYS_EXIT:  .equ  1
SYS_READ:  .equ  3
SYS_WRITE: .equ  4
SYS_OPEN:  .equ  5
SYS_CLOSE: .equ  6
} !elif OS == "linux" !then {
SYS_EXIT:  .equ  60
SYS_READ:  .equ  0
SYS_WRITE: .equ  1
SYS_OPEN:  .equ  2
SYS_CLOSE: .equ  3
} !else {
    !error "unknown OS: " + OS + " (use \"freebsd\" or \"linux\")"
}

; ===========================================================
; マクロ定義
; ===========================================================

; exit(code) -- code が 0 のときだけ xor で 3 バイト縮める
!def sysexit(code) {
    mov rax, SYS_EXIT
!if code == 0 !then {
    xor rdi, rdi
} !else {
    mov rdi, !{code}
}
    syscall
}

; prog_buf[r14] を al に読み込む (3箇所で使用)
!def load_op() {
    lea rax, [RIP+prog_buf]
    add rax, r14
    mov al, [rax]
}

; ディスパッチ表の1エントリ
!def case(ch, target) {
    cmp al, '!{ch}'
    je  !{target}
}

; rsi = &tape[r15], rdx = 1  (read/write の共通前処理)
!def tape_ptr_1byte() {
    mov rsi, tape_a        ; tape の絶対アドレス (imm64, R_X86_64_64)
    add rsi, r15
    mov rdx, 1
}

; 対応する括弧を探す走査ループ。
;   forward=1: r14 を前進させながら inc_ch で深度+1、dec_ch で深度-1
;   forward=0: r14 を後退させながら同上
; '[' 側と ']' 側は完全な鏡像なので、方向と文字の組だけを差し替える。
; ラベルは __id__ (呼び出しごとに一意) で生成するので、以前のように
; .inc_depth / .inc_depth2 と手で番号を振り分ける必要がない。
!def bracket_scan(forward, inc_ch, dec_ch) {
    mov rcx, 1             ; ネスト深度
.scan!{__id__}:
!if forward !then {
    inc r14
    cmp r14, r13
    jge exit
} !else {
    cmp r14, 0
    jle exit
    dec r14
}
    !load_op()
    cmp al, '!{inc_ch}'
    je  .deeper!{__id__}
    cmp al, '!{dec_ch}'
    je  .shallower!{__id__}
    jmp .scan!{__id__}
.deeper!{__id__}:
    inc rcx
    jmp .scan!{__id__}
.shallower!{__id__}:
    dec rcx
    cmp rcx, 0
    jne .scan!{__id__}
    jmp next
}

; ===========================================================
.section .text

_start:
    ; System V AMD64 ABI (FreeBSD 共通 linux:rdi->rsp):
    ;   プロセスエントリ時 RDI → argc, RDI+8 → argv[0], RDI+16 → argv[1]
!if OS == "freebsd" !then {
    mov  r8,rdi
} !else {
    mov  r8, rsp
}
    mov eax, [r8]         ; eax = argc
    cmp eax, 2
    jge  _open_file

    ; 引数不足: 使い方を stderr に表示して終了
    mov rax, SYS_WRITE
    mov rdi, 2
    lea rsi, [RIP+usage]
    mov rdx, usage_len
    syscall
    !sysexit(1)

_open_file:
    mov rax, r8
    add rax, 16            ; &argv[1]
    mov rdi, [rax]         ; argv[1] = ファイル名ポインタ
    mov rax, SYS_OPEN
    xor rsi, rsi           ; O_RDONLY = 0
    xor rdx, rdx
    syscall
    jc  exit_error
    jl  exit_error
    mov r12, rax           ; r12 = fd

    ; ファイルを prog_buf に一括読み込み
    mov rax, SYS_READ
    mov rdi, r12
    lea rsi, [RIP+prog_buf]
    mov rdx, !{PROG_SIZE}  ; バッファ確保と同じ定数から生成
    syscall
    mov r13, rax           ; r13 = プログラム長

    mov rax, SYS_CLOSE
    mov rdi, r12
    syscall

    ; 初期化
    xor r14, r14           ; 命令ポインタ = 0
    xor r15, r15           ; テープインデックス = 0

main_loop:
    cmp r14, r13
    jge exit

    ; 現在の BF 命令を al に読み込む
    !load_op()

!case(">", "op_inc_ptr")
!case("<", "op_dec_ptr")
!case("+", "op_inc_val")
!case("-", "op_dec_val")
!case(".", "op_output")
!case(",", "op_input")
!case("[", "op_loop_start")
!case("]", "op_loop_end")

next:
    inc r14
    jmp main_loop

; ===== Brainfuck 命令実装 =====

op_inc_ptr:
    inc r15                ; > : テープポインタを+1
    jmp next

op_dec_ptr:
    dec r15                ; < : テープポインタを-1
    jmp next

op_inc_val:
    inc byte [tape_a+r15]      ; + : 現在セルをインクリメント [SIB R_X86_64_32]
    jmp next

op_dec_val:
    dec byte [tape_a+r15]      ; - : 現在セルをデクリメント [SIB R_X86_64_32]
    jmp next

op_output:
    ; . : write(1, &tape[r15], 1)
    !tape_ptr_1byte()
    mov rax, SYS_WRITE
    mov rdi, 1
    syscall
    jmp next

op_input:
    ; , : read(0, &tape[r15], 1)
    !tape_ptr_1byte()
    mov rax, SYS_READ
    xor rdi, rdi
    syscall
    cmp rax, 0
    jle exit               ; EOF またはエラー
    jmp next

op_loop_start:
    ; [ : 現在セルが 0 なら対応する ']' の直後へジャンプ
    cmp byte [tape_a+r15], 0   ; [SIB R_X86_64_32]
    jne  next
!bracket_scan(1, "[", "]")

op_loop_end:
    ; ] : 現在セルが 0 でなければ対応する '[' の直後へ戻る
    cmp byte [tape_a+r15], 0   ; [SIB R_X86_64_32]
    je   next
!bracket_scan(0, "]", "[")

exit_error:
!sysexit(1)

exit:
!sysexit(0)

.section .data
usage:     .ascii "Usage: bf <file>",10
usage_len: .equ $$ - usage
.endsection

.section .bss
; SIB abs32 エイリアス:
;   INCB/DECB/CMPB [tape_a+r15] が R_X86_64_32 リロケーションを生成する
tape_a: .equ tape::abs32

tape:     .zero !{TAPE_SIZE}
prog_buf: .resb !{PROG_SIZE}
.endsection
