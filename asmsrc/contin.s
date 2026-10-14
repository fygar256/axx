; contin.s -- 行末の \ による行の継続（z80.axx、-v）。
; !include で取り込むファイルも継続をつなぐこと（以前は axx.py だけがつながなかった）と、
; ./ を含むパスで渡したソースの .include 先の名前が両実装で同じであること（以前は caxx.c
; だけが /.../././... のように畳まずに書いた）。test1 は ./ を付けたパスで組む。
        ld      a,\
5
!include "contin_inc.s"
        .include "contin_inc2.s"
        nop
