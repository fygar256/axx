; vliw_err.s -- vliw.axx で VLIW のパケットの誤りを確かめる（4 章）
;
; 2026-10-20 まで、空のスロット（`!!` の前や後ろが空）はパケットを黙って捨て、
; スロットに入りきらない命令は「warning-VLIW: ... truncating」と出して黙って
; 落としていた。どれもエラーにする。最後の行は正しいパケット。
;
;   axx vliw.axx vliw_err.s -b out.bin
ad r1,r2,r3!!
!!ad r1,r2,r3
ad r1,r2,r3!! !!!!
!!!!
ad r1,r2,r3!!ad r1,r2,r3!!ad r1,r2,r3!!ad r1,r2,r3!!ad r1,r2,r3!!!!
ad r1,r2,r3!!lod r1,[0x1234]!!jmp 0x9999!!!!
