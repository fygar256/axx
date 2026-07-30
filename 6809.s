; ============================================================
;  sample6809.s -- 6809.axx 動作確認用サンプルプログラム
;
;  fygar256/axx (汎用パターン駆動アセンブラ) 用に作成した
;  6809.axx パターンファイルで、MC6809 の代表的な命令・
;  アドレッシングモードを一通り使ってみるデモです。
;
;  含まれる内容:
;   - 文字列コピー   : ポストインクリメント間接 ,X+ / ,Y+
;   - サブルーチン呼び出し規約 : PSHS/PULS による任意順序の
;                        レジスタ退避・復帰
;   - 算術・比較・分岐 : ADDA/CMPA/BEQ/BGT/BRA など
;   - TFR/EXG        : レジスタ間転送・交換
;   - ジャンプテーブン: LEAX ...,PCR (PC相対) + JMP [B,X]
;                        (インデックス付き拡張間接ジャンプ)
;   - direct/extended の自動選択 (アドレス値に応じて
;                        1バイト/2バイトのアドレッシングを自動選択)
;   - データ定義     : FCB / FDB / .asciz
;   - 割り込みベクタテーブル (FFF0-FFFF)
;
;  アセンブル方法:
;   python3 axx.py 6809.axx sample6809.s -b sample6809.bin -v
; ============================================================

dpreg:  .equ    0
        .org    0x8000

start:
        lds     #0x7fff         ; スタックポインタ初期化
        ldx     #msg            ; コピー元(ROM上の文字列)
        ldy     #0x1000         ; コピー先(RAMバッファ、仮に0x1000番地とする)
        bsr     strcopy

        lda     #5
        ldb     #3
        bsr     add_and_check   ; 5+3 を計算し result へ格納

        ldb     #2
        bsr     jumptable_demo  ; ジャンプテーブル経由で case2 へ

main_loop:
        bra     main_loop       ; 以降は無限ループ(実機では割り込み待ちなど)

; ------------------------------------------------------------
; strcopy -- X が指すゼロ終端文字列を Y が指すアドレスへコピーする
;   任意順序のレジスタリストが正しく符号化されることを確認するため
;   退避時と復帰時でレジスタの並び順をあえて変えている
; ------------------------------------------------------------
strcopy:
        pshs    a,x,y
.loop1:
        lda     ,x+
        sta     ,y+
        cmpa    #0
        bne     .loop1
        puls    y,x,a
        rts

; ------------------------------------------------------------
; add_and_check -- A+B を計算し、結果に応じて分岐する
;   TFR/EXG、各種条件分岐、direct/extended 自動選択の確認
; ------------------------------------------------------------
add_and_check:
        pshs    b
        exg     a,b             ; A,B を交換
        adda    ,s+             ; スタック上の値(交換前のA)を加算しつつポップ
        cmpa    #8
        beq     .was_eight
        bgt     .too_big
        bra     .store
.was_eight:
        tfr     a,b             ; A の値を B へも転送
        bra     .store
.too_big:
        clra
.store:
        sta     result          ; direct/extended 自動選択アドレッシング
        rts

; ------------------------------------------------------------
; jumptable_demo -- B の値(0,1,2)に応じてジャンプテーブルへ分岐する
;   LEAX ...,PCR で PC相対にテーブル先頭アドレスを得て、
;   JMP [B,X] でインデックス付き拡張間接ジャンプを行う
; ------------------------------------------------------------
jumptable_demo:
        pshs    b
        leax    jtable,pcr
        lslb                    ; B*=2 (1エントリ2バイト)
        jmp     [b,x]

case0:
        ldb     #0
        bra     .jt_done
case1:
        ldb     #1
        bra     .jt_done
case2:
        ldb     #2
.jt_done:
        puls    b
        rts

; ------------------------------------------------------------
; データ定義
; ------------------------------------------------------------
jtable:
        fdb     case0
        fdb     case1
        fdb     case2

msg:
        .asciz  "HELLO 6809"

result:
        fcb     0x00

; ------------------------------------------------------------
; 割り込みベクタテーブル (Motorola MC6809 準拠)
; ------------------------------------------------------------
        .org    0xfff0
        fdb     0x0000          ; FFF0-FFF1  予約
        fdb     start           ; FFF2-FFF3  SWI3
        fdb     start           ; FFF4-FFF5  SWI2
        fdb     start           ; FFF6-FFF7  FIRQ
        fdb     start           ; FFF8-FFF9  IRQ
        fdb     start           ; FFFA-FFFB  SWI
        fdb     start           ; FFFC-FFFD  NMI
        fdb     start           ; FFFE-FFFF  RESET
