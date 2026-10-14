; riscv64full_edge.s -- riscv64full.axx の範囲の境目の回帰テスト（llvm-mc 19 と照合した値）。
; どの行も組めて、-b の像で比べる。c.lui の非ゼロ 6 ビットの即値は -32..-1 と 1..31
; （上位の形で 0xfffe0..0xfffff）。以前は -32 / 0xfffe0 を範囲外にしていた
        c.lui   a0, 0xfffe0
        c.lui   a0, -32
        c.lui   a0, 0xfffff
        c.lui   a0, 31
        c.addi  a0, -32
        c.addi16sp sp, -512
        c.addi4spn a0, sp, 1020
        c.j     $$+2046
        c.beqz  a0, $$-256
