; listinc.s -- -v の一覧で .include の行と include 先の行が 1 行ずつに分かれること、
; .section を書かないときの -o の .text が末尾の .org まで届くこと（z80.axx）
 NOP
 .include "listinc_inc.s"
 LD A,2
 .org 0x40
tail:
