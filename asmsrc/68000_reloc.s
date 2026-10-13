; 68000_reloc.s -- 68000.axx の -o（ELF32 M68K）の回帰テスト
;
;   caxx 68000.axx 68000_reloc.s -o 68000_reloc.o
;
; 型を書かない .extern は絶対 32 ビット（R_68K_32）。16 / 8 ビットの PC 相対は
; 値で見分けて R_68K_PC16 / R_68K_PC8 になり、同じセクションのラベルへは axx が
; 解決してリロケーションを出さない。外部への変位の範囲はリンカが確かめるので、
; .org で位置が 0x8000 を超えても範囲外にしない。加数は欄の幅で折り返して求める
; ので、その位置でも ext+0 / ext-1 のまま。
        .extern ext
        nop
        bra     ext             ; 裸の分岐も欄に参照が付く -> R_68K_PC8 ext-1
        bsr     ext
        beq.s   ext
        bra.w   ext             ; R_68K_PC16 ext+0
        bra.w   ext+4           ; R_68K_PC16 ext+4
        lea     ext(PC),A0      ; R_68K_PC16 ext+0
        lea     ext(PC,D0.W),A0 ; R_68K_PC8 ext+1（基点は拡張語）
        lea     ext+40000(PC),A1
        jsr     ext             ; R_68K_32
        move.l  #ext,D0         ; R_68K_32
        move.w  #ext,D0         ; R_68K_16
        move.l  ext,D1          ; R_68K_32
        move.w  (ext).W,D1      ; R_68K_16
        bra     loc             ; 同じセクション -> 解決する
        nop
loc:    rts
        .org    0x10000
        bra.w   ext             ; R_68K_PC16 ext+0
        bra.s   ext             ; R_68K_PC8 ext-1
        lea     ext(PC),A1
        dbra    D0,ext
