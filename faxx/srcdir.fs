\ srcdir.fs -- 出力バッファ (BinaryWriter) とソース側のディレクティブ

decimal

defer elf-sectioned? ( -- f )
: elf-sectioned?-nn63 false ; bind elf-sectioned?-nn63 elf-sectioned?

\ ---- 出力語の置き場 ----
variable wbuf  variable wset  variable wcap  variable omax
variable verbose  variable text-output  variable opt-debug
variable listing-open
variable out-file-a  variable out-file-u  variable has-outfile

: wbuf-init ( -- )
  1048576 wcap !
  wcap @ cells allocate throw wbuf !
  wcap @ allocate throw wset !
  wset @ wcap @ erase  0 omax ! ;
: wgrow ( need -- )
  dup wcap @ < if drop exit then
  wcap @ { old }
  begin dup wcap @ >= while wcap @ 2* wcap ! repeat drop
  wcap @ 134217728 > abort" output too large"
  wbuf @ wcap @ cells resize throw wbuf !
  wset @ wcap @ resize throw wset !
  wset @ old + wcap @ old - erase ;
: wmask ( -- u ) bts @ 64 >= if -1 else 1 bts @ lshift 1- then ;
: wstore ( pos val -- ) { pos val }
  bts @ 0<= if exit then
  pos 0< if exit then
  pos 1+ wgrow
  val wmask and wbuf @ pos cells + !
  1 wset @ pos + c!
  pos 1+ omax @ max omax ! ;
: hexw ( u width -- ) { u w }                              \ 0 詰めの小文字 16 進
  w 0 ?do
    u w 1- i - 4 * rshift 15 and dup 10 < if 48 + else 87 + then emit
  loop ;
: listing-on? ( -- f ) pass @ 2 = verbose @ and pass @ 0= or ;
: fwrite ( pos val prt -- ) { pos v prt }
  v wmask and { x }
  prt if
    s"  0x" type
    x bts @ 3 + 4 / hexw
  then
  pos x wstore ;
: outbin ( pos q -- ) @ swap { v pos }
  report? 0= if exit then
  pos v listing-on? fwrite ;
: outbin2 ( pos q -- ) @ swap { v pos }
  report? 0= if exit then
  pos v false fwrite ;
: outbin-n ( pos n -- ) qn outbin ;
: outbin2-n ( pos n -- ) qn outbin2 ;

\ ---- セクション ----
4 lazy-om sections                      \ 名前 -> [start size entry_pc confirmed]
variable nranges
create range-na 4096 cells allot  create range-nu 4096 cells allot
create range-s 4096 cells allot   create range-l 4096 cells allot
: range+ ( na nu s l -- ) { na nu s l }
  nranges @ 4096 >= if exit then
  na nu hdup nranges @ cells range-nu + !  nranges @ cells range-na + !
  s nranges @ cells range-s + !  l nranges @ cells range-l + !  1 nranges +! ;
: sec-entry ( a u -- slot ) sections om-put ;
: cur-section ( -- a u ) cur-sec-a @ cur-sec-u @ ;
: cur-section! ( a u -- ) hdup cur-sec-u ! cur-sec-a ! ;

\ ---- ディレクティブの補助 ----
: dir-rest-error ( a u idx name-a name-u -- stop? ) { a u idx na nu }
  a u idx over min /string trim { ra ru }
  ru 0= if false exit then
  mb-reset s"  error - " mb+ na nu mb+ s" : unexpected text after the argument: " mb+ ra ru repr1 mb+ s" ." mb+ mb-get diag-e
  true ;
: arg-eval ( a u -- v idx undef? ) false undef-flag !  0 expr-asm undef-flag @ ;

: dir-org ( l2a l2u -- ) { a u }
  a u arg-eval { v idx un }
  idx 1+ u < if a idx + c@ 44 = a idx 1+ + c@ uc 80 = and else false then { fill }
  a u idx fill if 2 + then s" .ORG" dir-rest-error if exit then
  un v qundef-derived? or if s"  error - .ORG argument contains undefined label." diag-e exit then
  v q-neg? if
    mb-reset s"  error - .ORG address must be non-negative, got " mb+ v q>dec mb+ s" ." mb+ mb-get diag-e exit
  then
  elf-sectioned? v @ pc @ < and if
    mb-reset s"  error - .ORG moves the location counter backwards (from " mb+ pc @ mb-n s"  to " mb+ v q>dec mb+
    s" ); an ELF object (-o, -E) cannot hold that." mb+ mb-get diag-e exit
  then
  fill if v @ pc @ > if
    v @ pc @ - dup 268435456 > if
      mb-reset s"  error - .ORG ,P fill count " mb+ dup mb-n s"  exceeds maximum 268435456." mb+ mb-get diag-e drop exit
    then
    0 ?do pc @ i + padding-v @ outbin2-n loop
  then then
  v @ pc ! ;
