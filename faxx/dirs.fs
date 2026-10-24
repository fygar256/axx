\ dirs.fs -- パターン側ディレクティブ (DirectiveProcessor の ELF 以外)

decimal

\ ---- 状態 ----
variable padding-v     \ 整数 (符号つき 64 ビットで足りる範囲を超えたら下位語)
variable bts           8 bts !
variable endian-big    false endian-big !
variable align-v       16 align-v !
variable passthru      variable eol-on    variable textmode
1 om-new constant chkmap              \ 変数 -> arr (許すシンボル、'' は省略可の印)
3 om-new constant enumdefs            \ 変数 -> [names arr][expr a][expr u]
1 om-new constant vartabs             \ 変数 -> om (名前 -> q)  (.unordered の .map)
1 om-new constant varnames            \ 使われた変数名 (.exp の検査用)
1 om-new constant freed-subs
0 constant pad-init
variable unordered-on

\ VLIW の状態
variable vliw-bits  variable vliw-instbits  variable vliw-tmplbits  variable vliw-flag
variable vliw-nopn                     \ NOP のバイト数
create vliw-nop 1024 allot
variable vliw-set                      \ EPIC の組の個数
create vliw-idx-a 256 cells allot      \ 各組の添字リスト (arr ポインタ)
create vliw-pat-a 256 cells allot
create vliw-pat-u 256 cells allot

\ エラー文言
2 om-new constant errtab               \ 10 進の番号 -> (a u) を値に持つ (value[0]=a [1]=u)
: errtab-init ( -- )
  errtab om-clear ;
: err-set ( code a u -- ) { c a u } c n>s errtab om-put a u hdup rot s! ;
: err-init ( -- )
  errtab-init
  1 s" Invalid syntax." err-set
  2 s" Address out of range." err-set
  3 s" Value out of range." err-set
  5 s" Register out of range." err-set
  6 s" Port number out of range." err-set ;
' err-init drop

: dir-var ( a u -- a' u' true | false )               \ 変数名 (小文字にして返す)
  trim 2dup var-name? 0= if 2drop false exit then slower 2dup varnames om-put drop true ;

\ 要素リストを展開する (elem_list_expand)。'' は省略可の印。
: count-ch ( a u c -- n ) { a u c } 0 u 0 ?do a i + c@ c = if 1+ then loop ;
: elem-list-expand ( a u -- l ) { a u }
  a u 44 count-ch 2 + lst-new { out }
  0 { st }
  u 1+ 0 ?do
    i u = a i + c@ 44 = or if
      a st + i st - trim supper { ta tu }
      ta tu s" " str=cs ta tu s\" \"\"" str=cs or ta tu s" ''" str=cs or if
        s" " out lst-add-str
      else
        ta tu asym-get ?dup if
          { arr } arr arr-n 0 ?do
            arr i arr-item item-kind 1 = if arr i arr-item item-str supper out lst-add-str
            else arr i arr-item item-q q>dec out lst-add-str then
          loop
        else ta tu out lst-add-str then
      then
      i 1+ to st
    then
  loop
  out ;

: omit-list-from-names ( l -- arr ) { l }               \ '' は 1 つだけ残す
  l lst-n 1+ lst-new { r }  false { sawo }
  l lst-n 0 ?do
    l i lst-item item-str { a u }
    u 0= if sawo 0= if s" " r lst-add-str true to sawo then
    else a u r lst-add-str then
  loop
  r arr-from-list ;

: chk-get ( a u -- arr|0 ) chkmap om-find ?dup if @ else 0 then ;
: chk-set ( a u arr -- ) { a u arr } a u chkmap om-put dup @ arr-free arr swap ! ;
: chk-del ( a u -- ) chkmap om-find ?dup if dup @ arr-free 0 swap ! then ;
: chk-clear-all ( -- ) chkmap om-used 0 ?do
    i chkmap om-live? if i chkmap om-val dup @ arr-free 0 swap ! then loop chkmap om-clear ;
: chk-del2 ( a u -- ) 2dup chk-del chkmap om-del ;

\ ---- .setsym ----
variable sym-target                    \ 数値シンボルの書き込み先 (numsyms か patsyms)
: sym-store-num ( ka ku q -- ) { ka ku q } ka ku sym-target @ om-put q swap q! ;

: exec-setsym ( row -- ) { r }
  r 1 rf trim { f1a f1u }  r 2 rf { f2a f2u }
  f1u if f1a f1u supper f2a f2u else
    f2u if f2a f2u trim supper 0 0 else
      s"  error - .setsym directive requires at least a symbol name" diag-e exit
    then
  then
  { ka ku va vu }
  \ ( 値欄 ) は va vu。f1u == 0 の場合 va vu は空
  va vu lstrip { la lu }
  lu 0> if la c@ 34 = else false then if
    ka ku la lu tmpl-inner ssym-set exit
  then
  lu 0> if la c@ 91 = else false then if
    ka ku la lu arr-items-from-text arr-from-list asym-set exit
  then
  ka ku la lu symbol-copy-from-name if exit then
  ka ku va vu symbol-set-from-text if exit then
  vu 0> if va vu 0 expr-pat drop else 0 qn then
  ka ku rot sym-store-num ;
