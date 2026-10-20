; labelc_err.s -- z80.axx で .labelc（5.1 節）が書いた行から後ろに効くことを確かめる
;
; .labelc は前のパスの最後の設定を持ち越さない。2026-10-20 まで、ファイルの後ろの
; .labelc が 2 回目以降の反復と pass 2 で先頭から効き、前に書いた end@x が
; ラベルとして通っていた。上の 2 行は構文エラー、下の 2 行は通る。
;
;   axx z80.axx labelc_err.s -b out.bin
        jp      end@x
end@x:  nop
.labelc @
foo@:   nop
        jp      foo@
