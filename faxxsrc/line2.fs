\ line2.fs -- 1 命令の組み立て (Assembler.lineassemble2): 候補の索引、最良の照合、出力ワード

decimal

\ ---- ELF / マクロ / VLIW が差し込む口 ----
defer elf-src-dir ( la lu l2a l2u -- handled? )        \ .extern .global .type .size .weak ... .comm .cfi_*
: elf-src-dir-nn23 2drop 2drop false ; bind elf-src-dir-nn23 elf-src-dir
defer asm-include ( a u -- )                           \ .include の実体 (fileassemble)
: asm-include-nn24 2drop ; bind asm-include-nn24 asm-include
defer snap-extra-take ( -- )                            \ ELF の表の写し
: snap-extra-take-nn25 ; bind snap-extra-take-nn25 snap-extra-take
defer snap-extra-restore ( -- )
: snap-extra-restore-nn26 ; bind snap-extra-restore-nn26 snap-extra-restore
defer lineclear-extra ( -- )                            \ 行ごとに消す ELF の表
: lineclear-extra-nn27 ; bind lineclear-extra-nn27 lineclear-extra
defer cand-begin ( -- )                                 \ 候補ごとの追跡の起点 (ELF のラベル参照)
: cand-begin-nn28 ; bind cand-begin-nn28 cand-begin
defer cand-end-fail ( -- )
: cand-end-fail-nn29 ; bind cand-end-fail-nn29 cand-end-fail

: vliw-sep? ( c -- f ) dup VLIW-SEP-C = swap VLIW-STOP-C = or ;

\ ---- 語を読む ----
: p-spc ( a u i -- ta tu i' ) { a u i }                  \ get_param_to_spc
  begin i u < if a i + c@ spc? else false then while i 1+ to i repeat
  i { st }
  begin i u < if a i + c@ dup 32 <> swap vliw-sep? 0= and else false then while i 1+ to i repeat
  a st + i st - i ;
: p-eon ( a u i -- ta tu i' ) { a u i }                  \ get_param_to_eon
  begin i u < if a i + c@ spc? else false then while i 1+ to i repeat
  i { st }
  begin i u < if a i + c@ vliw-sep? 0= else false then while i 1+ to i repeat
  a st + i st - i ;
: rstrip-st ( a u -- a u' ) begin dup 0> if 2dup + 1- c@ dup 32 = swap 9 = or else false then while 1- repeat ;
: strip-spaces ( a u -- a' u' ) { a u }                  \ 空白を全部落とす
  u 1+ ar-alloc { d } 0 { n }
  u 0 ?do a i + c@ dup 32 <> if d n + c! n 1+ to n else drop then loop
  d n ;
\ ---- 出力語の道具 ----
: obj-reset ( -- ) 0 nobj ! ;
: obj-prepend ( a u -- ) { a u }                         \ 先頭にバイト列を差し込む
  nobj @ u + MAXOBJ > abort" binary_list too long"
  objl objl u QB * + nobj @ QB * move
  u 0 ?do a i + c@ qn objl i QB * + q! loop
  u nobj +! ;
: text-words ( a u -- )                                  \ UTF-8 の 1 バイトが 1 語
  { a u }
  u 0 ?do a i + c@ obj-byte loop ;
: asm-text! ( a u -- ) { a u }
  asmtext-clear  true asmtext-set !
  a u asmtext sb+
  34 asmdisp sb-c  a u asmdisp txt-escaped  34 asmdisp sb-c ;

: text-warn ( a u -- ) { a u }
  wmask { m } false { over }
  u 0 ?do a i + c@ m u> if true to over then loop
  over size-mode @ 0= and report? and if
    mb-reset s"  warning - .passthru: one or more bytes exceed the output word width (" mb+ bts @ mb-n
    s"  bit(s)) and were truncated (high bits discarded): " mb+ a u repr1 mb+ mb-get diag-w
  then ;

\ ---- 戻り値 ----
: l2-done ( idx -- idxs flag idx ) q0 true rot ;
: l2-fail ( idx -- idxs flag idx ) q0 false rot ;
: passthru-line ( la lu l2a l2u idx -- idxs flag idx ) { la lu l2a l2u idx }
  l2u if la lu s"  " sconcat l2a l2u sconcat else la lu then { ta tu }
  false undef-flag !
  obj-reset
  ta tu text-warn
  ta tu text-words
  ta tu asm-text!
  idx l2-done ;
: dir-line-done ( la lu l2a l2u idx -- idxs flag idx )
  textmode @ if passthru-line exit then
  nip nip nip nip l2-done ;

MAXROWS cells lazy dirorder
variable dirorder-n

\ ---- パターン索引 ----
MAXROWS cells lazy pn-next
MAXROWS cells lazy palways
variable npalways
2 lazy-om pidx                         \ 先頭大文字列 -> [開いた先頭 row+1][閉じた先頭 row+1]
variable pmaxkey
MAXROWS cells lazy cand
variable ncand

: pfx-word? ( c -- f ) dup alnc? swap 95 = or ;
: pfx-open? ( c -- f ) dup lowc? over digc? or swap dup 33 = swap dup 92 = swap dup 91 = swap 95 = or or or or ;
lazy-sb lc-b
: lead-caps ( a u -- pa pu closed ) { a u } 0 { k }
  lc-b sb-clear
  begin k u < if a k + c@ dup capc? swap 32 = or else false then while
    a k + c@ dup 32 <> if lc-b sb-c else drop then
    k 1+ to k
  repeat
  k u < if a k + c@ pfx-open? 0= else true then
  lc-b sb$ rot ;

: row-blank? ( r -- f ) true { b } 6 0 ?do dup i rf nip 0<> if false to b then loop drop b ;

: build-pat-index ( -- )
  pidx om-clear  0 npalways !  0 pmaxkey !
  pn-next nrows @ cells erase
  nrows @ 0 ?do
    i risdir @ if
      i row-blank? 0= if i palways npalways @ cells + ! 1 npalways +! then
    else
      i rf0 lead-caps { closed } { pa pu }
      pu 0= if
        i row-blank? 0= if i palways npalways @ cells + ! 1 npalways +! then
      then
    then
  loop
  \ 索引は降順に積んで、先頭から読むと昇順になるようにする
  nrows @ 0> if 0 nrows @ 1- do
    i risdir @ 0= if
      i rf0 lead-caps { closed } { pa pu }
      pu 0> if
        pa pu pidx om-put { sl }
        closed if 1 else 0 then { w }
        sl w cells + @ pn-next i cells + !   \ row i の次 = 旧い先頭
        i 1+ sl w cells + !
        pu pmaxkey @ max pmaxkey !
      then
    then
  -1 +loop then ;

: push-list ( head -- ) begin dup 0<> while 1- dup cand ncand @ cells + ! 1 ncand +! cells pn-next + @ repeat drop ;

: sort-cand ( -- )
  ncand @ 1 ?do
    cand i cells + @ { v } i { j }
    begin j 0> if cand j 1- cells + @ v > else false then while
      cand j 1- cells + @ cand j cells + !  j 1- to j
    repeat
    v cand j cells + !
  loop ;

create keybuf 64 allot
create nextraw 64 allot
: gather-cands ( a u -- ) { a u } 0 ncand !
  pmaxkey @ 0= if exit then
  0 { nk }
  u 0 ?do
    a i + c@ 32 <> if
      a i + c@ uc keybuf nk + c!
      i 1+ u < if a i 1+ + c@ else 0 then nextraw nk + c!
      nk 1+ to nk
      nk pmaxkey @ >= if leave then
    then
  loop
  nk 0 ?do
    keybuf i 1+ pidx om-find ?dup if
      { sl }
      sl @ push-list
      nextraw i + c@ pfx-word? 0= if sl cell+ @ push-list then
    then
  loop
  ncand @ 1 > if sort-cand then ;

\ ---- 候補の中の最良 ----
variable best-row
create best-score 3 cells allot
variable best-undef
lazy-sb best-diag
variable snap-live                    \ 最良の時点の状態を写してあるか
variable snap-need                    \ 最良の後でディレクティブが動いたか

\ ディレクティブ状態の写し (SNAP_*)
create sv-sw 256 allot
create sv-nop 1024 allot
variable sv-endian variable sv-bts variable sv-pad
variable sv-vb variable sv-vi variable sv-vt variable sv-vf variable sv-vnn variable sv-vset
create sv-vidx 256 cells allot  create sv-vpa 256 cells allot  create sv-vpu 256 cells allot
4 lazy-om sv-psyms
1 lazy-om sv-chk
3 lazy-om sv-enum

: chk-copy ( src dst -- ) { src dst }                   \ 配列まで複写する
  dst om-used 0 ?do i dst om-live? if i dst om-val dup @ arr-free 0 swap ! then loop
  dst om-clear
  src om-used 0 ?do
    i src om-live? if
      i src om-key dst om-put
      i src om-val @ ?dup if arr-clone else 0 then swap !
    then
  loop ;

: snap-take ( -- )
  endian-big @ sv-endian !  bts @ sv-bts !  padding-v @ sv-pad !
  sw-tab sv-sw 256 move
  vliw-bits @ sv-vb !  vliw-instbits @ sv-vi !  vliw-tmplbits @ sv-vt !  vliw-flag @ sv-vf !
  vliw-nopn @ sv-vnn !  vliw-nop sv-nop 1024 move
  vliw-set @ sv-vset !
  vliw-idx-a sv-vidx 256 cells move  vliw-pat-a sv-vpa 256 cells move  vliw-pat-u sv-vpu 256 cells move
  numsyms sv-psyms om-copy
  chkmap sv-chk chk-copy
  enumdefs sv-enum om-copy
  snap-extra-take
  true snap-live ! ;
: snap-restore ( -- )
  sv-endian @ endian-big !  sv-bts @ bts !  sv-pad @ padding-v !
  sv-sw sw-tab 256 move
  sv-vb @ vliw-bits !  sv-vi @ vliw-instbits !  sv-vt @ vliw-tmplbits !  sv-vf @ vliw-flag !
  sv-vnn @ vliw-nopn !  sv-nop vliw-nop 1024 move
  sv-vset @ vliw-set !
  sv-vidx vliw-idx-a 256 cells move  sv-vpa vliw-pat-a 256 cells move  sv-vpu vliw-pat-u 256 cells move
  sv-psyms numsyms om-copy
  sv-chk chkmap chk-copy
  sv-enum enumdefs om-copy
  snap-extra-restore ;

: dir-modifies? ( kind -- f )
  dup 13 = over 14 = or over 15 = or over 18 = or over 19 = or swap 20 = or 0= ;

\ ---- ディレクティブ行を実行 ----
variable nsym-dirty  true nsym-dirty !
: run-dir-row ( row -- )
  dup rkind @ dir-modifies? if
    best-row @ 0>= snap-live @ 0= and if snap-take then
  then
  dup rkind @ dup 1 = over 2 = or over 11 = or swap 12 = or if true nsym-dirty ! then
  vars-reset
  0 exec-dir ;

: exec-unordered ( -- ) dirorder-n @ 0 ?do i cells dirorder + @ vars-reset 0 exec-dir loop ;

\ 候補 1 行の試行。成功なら true。
: try-row ( row -- ok ) { row }
  false undef-flag !
  vars-reset
  trk-cand-begin
  cand-begin
  true in-match !
  pend-begin
  row match-row { ok }
  false in-match !
  pend-take { da du }
  ok if
    n-expr @ { e }  n-lit @ negate { l }  n-sym @ { s }
    best-row @ 0< if true else
      e best-score @ < if true else
        e best-score @ = if
          l best-score cell+ @ < if true else
            l best-score cell+ @ = s best-score 2 cells + @ < and
          then
        else false then
      then
    then
    if
      row best-row !
      trk-cand-best
      e best-score !  l best-score cell+ !  s best-score 2 cells + !
      undef-flag @ best-undef !
      best-diag sb-clear  da du best-diag sb+
      vsave
      false snap-live !
    then
    vars-reset
  else cand-end-fail then
  trk-cand-restore
  false undef-flag !
  ok ;

\ ---- 1 行 ----
defer vliw-sentinel-hook ( -- )
: vliw-sentinel-hook-nn30 ; bind vliw-sentinel-hook-nn30 vliw-sentinel-hook

: pass1-probe ( row -- ) { row }
  pc @ pc-start !  pc-start @ pc-end !
  size-mode @ { sm }  true size-mode !
  trk-probe-begin
  row 2 rf makeobj
  trk-probe-end
  pc-start @ nobj @ + pc-end !
  sm size-mode !
  best-undef @ undef-flag ! ;


\ ---- ソース側ディレクティブの振り分け ----
: is? ( a u pa pu -- a u f ) 2>r 2dup 2r> str=cs ;
: is2? ( a u p1a p1u p2a p2u -- a u f ) { a u pa pu qa qu } a u  a u pa pu str=cs a u qa qu str=cs or ;
: text-only-dir? ( ua uu -- f )
  s" .ORG" is? >r s" .ALIGN" is? r> or >r s" .ZERO" is? r> or >r
  s" .ASCII" is? r> or >r s" .ASCIZ" is? r> or >r
  s" .RESB" is? r> or >r s" .RESW" is? r> or >r s" .RESD" is? r> or >r s" .RESQ" is? r> or >r
  s" .DB" is? r> or >r s" .DW" is? r> or >r s" .DD" is? r> or >r s" .DQ" is? r> or >r
  s" .DO" is? r> or >r s" .DY" is? r> or >r s" .DZ" is? r> or
  nip nip ;

variable sd-la variable sd-lu variable sd-l2a variable sd-l2u variable sd-i2
: sd-done ( -- idxs flag idx ) sd-la @ sd-lu @ sd-l2a @ sd-l2u @ sd-i2 @ dir-line-done ;
: sd-plain ( -- idxs flag idx ) sd-i2 @ l2-done ;
: sd-l2 ( -- a u ) sd-l2a @ sd-l2u @ ;

\ ソース側のディレクティブなら処理して (idxs flag idx true)、そうでなければ false
: src-directive ( ua uu -- idxs flag idx true | false )
  s" .SECTION" s" .SEGMENT" is2? if 2drop sd-l2 dir-section sd-done true exit then
  s" .ENDSECTION" s" .ENDSEGMENT" is2? if 2drop dir-endsection sd-done true exit then
  s" .RESB" is? if 2drop sd-l2 s" .RESB" 1 dir-res sd-done true exit then
  s" .RESW" is? if 2drop sd-l2 s" .RESW" 2 dir-res sd-done true exit then
  s" .RESD" is? if 2drop sd-l2 s" .RESD" 4 dir-res sd-done true exit then
  s" .RESQ" is? if 2drop sd-l2 s" .RESQ" 8 dir-res sd-done true exit then
  s" .ZERO" is? if 2drop sd-l2 dir-zero sd-done true exit then
  s" .DB" is? if 2drop sd-l2 s" .DB" 1 dir-data sd-plain true exit then
  s" .DW" is? if 2drop sd-l2 s" .DW" 2 dir-data sd-plain true exit then
  s" .DD" is? if 2drop sd-l2 s" .DD" 4 dir-data sd-plain true exit then
  s" .DQ" is? if 2drop sd-l2 s" .DQ" 8 dir-data sd-plain true exit then
  s" .DO" is? if 2drop sd-l2 s" .DO" 16 dir-data sd-plain true exit then
  s" .DY" is? if 2drop sd-l2 s" .DY" 32 dir-data sd-plain true exit then
  s" .DZ" is? if 2drop sd-l2 s" .DZ" 64 dir-data sd-plain true exit then
  s" .ASCII" is? if 2drop sd-l2 dir-ascii sd-plain true exit then
  s" .ASCIZ" is? if 2drop sd-l2 dir-asciz sd-plain true exit then
  s" .INCLUDE" is? if
    2drop sd-l2 asm-include comment-text sb-clear indent-text sb-clear 0 nobj ! sd-plain true exit then
  s" .ALIGN" is? if 2drop sd-l2 dir-align sd-done true exit then
  s" .ORG" is? if 2drop sd-l2 dir-org sd-done true exit then
  s" .LABELC" is? if 2drop sd-l2 dir-labelc sd-done true exit then
  2drop
  sd-la @ sd-lu @ sd-l2a @ sd-l2u @ elf-src-dir if sd-done true exit then
  false ;

\ ---- 候補の走査 ----
variable sc-sent  variable sc-idxs
: pick-row ( ai ci -- row ai' ci' ) { ai ci }
  ai npalways @ < { ha }  ci ncand @ < { hc }
  ha hc and if
    ai cells palways + @  ci cells cand + @ { ar cr }
    cr ar < if cr ai ci 1+ else ar ai 1+ ci then
  else ha if ai cells palways + @ ai 1+ ci else ci cells cand + @ ai ci 1+ then then ;

: scan-patterns ( -- )
  false sc-sent !  q0 sc-idxs !
  0 0 { ai ci }
  begin ai npalways @ < ci ncand @ < or while
    ai ci pick-row to ci to ai { row }
    row risdir @ if
      row run-dir-row
    else row row-blank? 0= if
      row rf0 nip 0= if
        true sc-sent !
        best-row @ 0< if vars-reset  row 3 rf 0 expr-pat drop sc-idxs ! then
        npalways @ to ai  ncand @ to ci
      else
        ar-mark { mk }
        row try-row drop
        best-row @ row <> if mk ar-release then
      then
    then then
  repeat ;

\ ---- 最良の候補を実行する ----
: run-best ( -- idxs )
  snap-live @ if snap-restore then
  vrestore
  trk-best-install
  best-undef @ undef-flag !
  best-diag sb$ pend-replay
  best-row @ { br }
  br pass1-probe
  br 1 rf error-eval 0= if br 2 rf makeobj else 0 nobj ! then
  br 3 rf 0 expr-pat drop ;

lazy-sb loc-b
: loc-text ( -- a u )
  loc-b sb-clear  s"   [" loc-b sb+  file@ loc-b sb+  s" :" loc-b sb+  line-no @ n>s loc-b sb+  s" ]" loc-b sb+
  loc-b sb$ ;

: lineassemble2 ( a u idx -- idxs flag idx ) { a u idx0 }
  a u idx0 p-spc { la lu i1 }
  a u i1 p-eon { l2a l2u i2 }
  la lu rstrip-st strip-spaces to lu to la
  l2a l2u rstrip-st to l2u to l2a
  la sd-la !  lu sd-lu !  l2a sd-l2a !  l2u sd-l2u !  i2 sd-i2 !
  false undef-flag !  0 nobj !  false data-line !
  la lu supper { ua uu }
  textmode @ if ua uu text-only-dir? if la lu l2a l2u i2 passthru-line exit then then
  ua uu src-directive if exit then
  lu 0= if
    textmode @ if label-text sb-len comment-text sb-len or 0<> else false then if
      i2 l2-done exit then
    i2 l2-fail exit
  then
  l2u if la lu s"  " sconcat l2a l2u sconcat else la lu then reduce-spaces sdup { lin-a lin-u }
  lin-a ms-a !  lin-u ms-u !
  -1 best-row !  false snap-live !
  -1 best-score !  0 best-score cell+ !  0 best-score 2 cells + !
  lin-a lin-u gather-cands
  unordered-on @ if exec-unordered then
  scan-patterns
  q0 { idxs }  0 nobj !
  best-row @ 0>= if run-best to idxs
  else sc-sent @ if sc-idxs @ to idxs then then
  best-row @ 0< sc-sent @ 0= and { se }
  se passthru @ and if la lu l2a l2u i2 passthru-line exit then
  report? if
    undef-flag @ if
      true had-error !
      mb-reset s"  error - Undefined label in expression." mb+ loc-text mb+ mb-get diag-w
      i2 l2-fail exit
    then
    se if
      true had-error !
      mb-reset s"  error - Syntax error." mb+ loc-text mb+ mb-get diag-w
      i2 l2-fail exit
    then
  then
  idxs true i2 ;
