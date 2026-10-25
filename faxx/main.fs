\ main.fs -- コマンドライン、パスの制御 (Assembler.run)

decimal

\ ---- 診断の補助 ----
: eput ( a u -- ) etype ;
: ecrlf ( -- ) ecr ;
: fatal-w ( a u -- ) diag-wf ;                      \ force 付きの診断 (set_error=False)

\ ---- 引数の値 ----
variable o-pat-a   variable o-pat-u
variable o-src-a   variable o-src-u    variable o-src?
variable o-exp-a   variable o-exp-u
variable o-expe-a  variable o-expe-u
variable o-imp-a   variable o-imp-u
variable o-obj-a   variable o-obj-u
variable o-osabi-a variable o-osabi-u
variable o-fmt     variable o-machine  variable o-machine?
variable o-nomacro variable o-elfdesc
variable o-mx-a     variable o-mx-u      variable o-mx?
variable o-mp-a     variable o-mp-u      variable o-mp?
variable o-help
variable o-npos

: opts-init ( -- )
  0 o-pat-a ! 0 o-pat-u !  0 o-src-a ! 0 o-src-u ! false o-src? !
  0 o-exp-a ! 0 o-exp-u !  0 o-expe-a ! 0 o-expe-u !  0 o-imp-a ! 0 o-imp-u !
  0 o-obj-a ! 0 o-obj-u !  s" Linux" o-osabi-u ! o-osabi-a !
  0 o-fmt !  0 o-machine !  false o-machine? !
  false o-nomacro !  false o-elfdesc !  false o-mx? !  false o-mp? !  false o-help !  0 o-npos !
  0 out-file-a !  0 out-file-u !  false has-outfile !
  false verbose !  false text-output !  false opt-debug !  false gen-debug ! ;

: usage-text ( -- )
  help-text 0 { a u pos }
  \ 最初の空行 (usage の終わり) まで
  a u { ha hu }
  hu 0 ?do
    ha i + c@ 10 = if
      i 1+ hu < if ha i 1+ + c@ 10 = if ha i 1+ eput unloop exit then then
    then
  loop
  ha hu eput ;
: arg-error ( a u -- )
  usage-text  s" axx: error: " eput eput ecr  2 (bye) ;

\ -P / -p の省略可能なファイル名を引数の並びから拾う (_normalise_macro_expand_argv)
\ 引数を配列に集めてから解釈する
256 constant MAXARGS
create av-a MAXARGS cells allot   create av-u MAXARGS cells allot
variable av-n
: collect-args ( -- )
  0 av-n !
  begin next-arg dup 0> while
    av-n @ MAXARGS >= if 2drop else sdup av-n @ cells av-u + ! av-n @ cells av-a + ! 1 av-n +! then
  repeat 2drop ;
: av@ ( i -- a u ) dup cells av-a + @ swap cells av-u + @ ;

: with-arg? ( a u -- f )
  2dup s" --osabi" str=cs >r 2dup s" -b" str=cs r> or >r 2dup s" -e" str=cs r> or >r
  2dup s" -E" str=cs r> or >r 2dup s" -f" str=cs r> or >r 2dup s" -i" str=cs r> or >r
  2dup s" -o" str=cs r> or >r s" -m" str=cs r> or ;

\ 整数の引数 (argparse の int)
: parse-int ( a u -- n ok ) { a u }
  a u trim to u to a
  u 0= if 0 false exit then
  false { neg } 0 { k }
  a c@ 45 = if true to neg 1 to k else a c@ 43 = if 1 to k then then
  k u >= if 0 false exit then
  0 begin k u < while
    a k + c@ digc? 0= if drop 0 false unloop exit then
    10 * a k + c@ 48 - + k 1+ to k
  repeat
  neg if negate then true ;

: need-arg ( i opt-a opt-u -- a u ) { i oa ou }
  i 1+ av-n @ >= if
    mb-reset s" argument " mb+ oa ou mb+ s" : expected one argument" mb+ mb-get arg-error
  then
  i 1+ av@ ;

: o-outfile-set ( a u -- ) hdup out-file-u ! out-file-a ! true has-outfile ! ;
: set-str ( a u va vu -- ) { a u va vu } a u hdup vu ! va ! ;

\ 引数 1 つぶん。i は添字。返り値は進めたあとの添字
: parse-opt ( i -- i' ) { i }
  i av@ { a u }
  a u s" -h" str=cs a u s" --help" str=cs or if true o-help ! i 1+ exit then
  a u s" -v" str=cs a u s" --verbose" str=cs or if true verbose ! i 1+ exit then
  a u s" -V" str=cs a u s" --text-output" str=cs or if true text-output ! i 1+ exit then
  a u s" -d" str=cs a u s" --debug" str=cs or if true opt-debug ! i 1+ exit then
  a u s" -g" str=cs a u s" --gen-debug" str=cs or if true gen-debug ! i 1+ exit then
  a u s" --no-macro" str=cs if true o-nomacro ! i 1+ exit then
  a u s" --elfdesc" str=cs if true o-elfdesc ! i 1+ exit then
  a u s" -b" str=cs if i s" -b" need-arg o-outfile-set i 2 + exit then
  a u s" -e" str=cs if i s" -e" need-arg o-exp-a o-exp-u set-str i 2 + exit then
  a u s" -E" str=cs if i s" -E" need-arg o-expe-a o-expe-u set-str i 2 + exit then
  a u s" -i" str=cs if i s" -i" need-arg o-imp-a o-imp-u set-str i 2 + exit then
  a u s" -o" str=cs if i s" -o" need-arg o-obj-a o-obj-u set-str i 2 + exit then
  a u s" --osabi" str=cs if i s" --osabi" need-arg o-osabi-a o-osabi-u set-str i 2 + exit then
  a u s" -f" str=cs if
    i s" -f" need-arg 2dup parse-int if
      dup 32 = over 64 = or if o-fmt ! 2drop i 2 + exit then
      drop
    else drop then
    mb-reset s" argument -f: invalid choice: " mb+ 2dup repr1 mb+ s"  (choose from 32, 64)" mb+ mb-get arg-error
  then
  a u s" -m" str=cs if
    i s" -m" need-arg 2dup parse-int if
      o-machine ! 2drop true o-machine? ! i 2 + exit
    then
    drop mb-reset s" argument -m: invalid int value: " mb+ repr1 mb+ mb-get arg-error
  then
  a u s" -P" str=cs a u s" --macro-expand" str=cs or if
    true o-mx? !  s" -" o-mx-u ! o-mx-a !
    i 1+ av-n @ < if
      i 1+ av@ { na nu }
      na nu s" -" str=cs if i 2 + exit then
      na c@ 45 <> nu 0> and if
        o-npos @ 2 >= if na nu o-mx-a o-mx-u set-str i 2 + exit then
        mb-reset s"  error - '" mb+ a u mb+ s"  " mb+ na nu mb+ s" ' is ambiguous here: " mb+ na nu repr1 mb+
        s"  could be " mb+ a u mb+ s" 's output file or a positional argument. Write '--macro-expand=" mb+ na nu mb+
        s" ', or put " mb+ a u mb+ s"  after the pattern/source files." mb+ mb-get diag-wf 2 (bye)
      then
    then
    i 1+ exit
  then
  a u s" -p" str=cs a u s" --macro-expand-pattern" str=cs or if
    true o-mp? !  s" -" o-mp-u ! o-mp-a !
    i 1+ av-n @ < if
      i 1+ av@ { na nu }
      na nu s" -" str=cs if i 2 + exit then
      na c@ 45 <> nu 0> and if
        o-npos @ 1 >= if na nu o-mp-a o-mp-u set-str i 2 + exit then
        mb-reset s"  error - '" mb+ a u mb+ s"  " mb+ na nu mb+ s" ' is ambiguous here: " mb+ na nu repr1 mb+
        s"  could be " mb+ a u mb+ s" 's output file or a positional argument. Write '--macro-expand-pattern=" mb+ na nu mb+
        s" ', or put " mb+ a u mb+ s"  after the pattern file." mb+ mb-get diag-wf 2 (bye)
      then
    then
    i 1+ exit
  then
  \ --opt=value
  a u 61 find-ch { eq }
  eq u < a c@ 45 = and a 1+ c@ 45 = and if
    a eq s" --macro-expand" str=cs if true o-mx? ! a eq 1+ + u eq 1+ - hdup o-mx-u ! o-mx-a ! i 1+ exit then
    a eq s" --macro-expand-pattern" str=cs if true o-mp? ! a eq 1+ + u eq 1+ - hdup o-mp-u ! o-mp-a ! i 1+ exit then
    a eq s" --osabi" str=cs if a eq 1+ + u eq 1+ - o-osabi-a o-osabi-u set-str i 1+ exit then
  then
  \ -bFILE のような結合形
  u 2 > a c@ 45 = and a 1+ c@ 45 <> and if
    a 1+ c@ case
      98 of a 2 + u 2 - o-outfile-set i 1+ exit endof
      101 of a 2 + u 2 - o-exp-a o-exp-u set-str i 1+ exit endof
      69 of a 2 + u 2 - o-expe-a o-expe-u set-str i 1+ exit endof
      105 of a 2 + u 2 - o-imp-a o-imp-u set-str i 1+ exit endof
      111 of a 2 + u 2 - o-obj-a o-obj-u set-str i 1+ exit endof
    endcase
    \ -vd のような旗の連なり
    true { allflags }
    u 1 ?do a i + c@ dup 118 = over 86 = or over 100 = or over 103 = or swap 104 = or 0= if false to allflags then loop
    allflags if
      u 1 ?do a i + c@ case
        118 of true verbose ! endof  86 of true text-output ! endof
        100 of true opt-debug ! endof  103 of true gen-debug ! endof
        104 of true o-help ! endof
      endcase loop
      i 1+ exit
    then
  then
  a c@ 45 = u 1 > and if
    mb-reset s" unrecognized arguments: " mb+ a u mb+ mb-get arg-error
  then
  \ 位置引数
  o-npos @ 0= if a u o-pat-a o-pat-u set-str 1 o-npos ! else
  o-npos @ 1 = if a u o-src-a o-src-u set-str true o-src? ! 2 o-npos ! else
    mb-reset s" unrecognized arguments: " mb+ a u mb+ mb-get arg-error
  then then
  i 1+ ;

\ ---- ラベルの取り込み (-i) ----
: imp-hex ( a u -- v ok ) { a u }
  a u trim to u to a
  false { neg } 0 { k }
  u 0= if q0 false exit then
  a c@ 45 = if true to neg 1 to k else a c@ 43 = if 1 to k then then
  k 1+ u < if a k + c@ 48 = a k 1+ + c@ uc 88 = and if k 2 + to k then then
  k u >= if q0 false exit then
  q0 { v }  0 { nd }
  begin k u < while
    a k + c@ xdig? 0= if q0 false exit then
    a k + c@ hexv { dv }
    v 16 dv q*small+ drop to v
    nd 1+ to nd  k 1+ to k
  repeat
  v qnbit 192 > if q0 false exit then
  neg if v qneg else v then true ;

variable imp-sec-n
create imp-sec-a 4096 cells allot  create imp-sec-u 4096 cells allot
4096 QB * allocate throw constant imp-sec-s
4096 QB * allocate throw constant imp-sec-z

defer reloc-named ( a u -- n )             \ 名前から再配置の型。分からなければ -1
:noname 2drop -1 ; is reloc-named

create tf-a 8 cells allot   create tf-u 8 cells allot
: split-tabs ( a u -- n ) { a u }                   \ 最初の 4 欄を tf-a / tf-u へ。欄の数 (全部) を返す
  0 { n } 0 { st }
  u 0 ?do
    a i + c@ 9 = if
      n 4 < if a st + n cells tf-a + !  i st - n cells tf-u + ! then
      n 1+ to n  i 1+ to st
    then
  loop
  n 4 < if a st + n cells tf-a + !  u st - n cells tf-u + ! then
  n 1+ ;

: imp-section-line ( a u -- ) { a u }
  tf-a 1 cells + @ tf-u 1 cells + @ imp-hex 0= if drop exit then { start }
  tf-a 2 cells + @ tf-u 2 cells + @ imp-hex 0= if drop exit then { size }
  imp-sec-n @ 4096 >= if exit then
  tf-a @ tf-u @ intern imp-sec-n @ cells imp-sec-u + ! imp-sec-n @ cells imp-sec-a + !
  start imp-sec-n @ QB * imp-sec-s + q!
  size imp-sec-n @ QB * imp-sec-z + q!
  1 imp-sec-n +! ;

: imp-label-line ( -- )
  tf-a @ tf-u @ { la lu }
  lu 0= if exit then
  -1 { rt }
  la lu s" ::" 0 str-pos { cp }
  cp 0>= if
    la cp + 2 + lu cp - 2 - slower { ra ru }
    la cp to lu  la to la
    ra ru reloc-named to rt
    rt 0< if
      mb-reset s"  warning - unknown reloc type '" mb+ ra ru mb+ s" ' for imported label '" mb+ la lu mb+ s" '" mb+ mb-get diag-w
    then
  then
  lu 0= if exit then
  tf-a 1 cells + @ tf-u 1 cells + @ imp-hex 0= if drop exit then { v }
  s" .text" { sa su }
  imp-sec-n @ 0 ?do
    i QB * imp-sec-s + { st }  i QB * imp-sec-z + { sz }
    sz q-neg? 0= sz q-zero? 0= and if
      v st q>= v st sz q+ q< and if i cells imp-sec-a + @ i cells imp-sec-u + @ to su to sa leave then
    else sz q-zero? if
      v st q= if i cells imp-sec-a + @ i cells imp-sec-u + @ to su to sa leave then
    then then
  loop
  bts @ 7 + 8 / 1 max { bpw }
  v bpw qn qfloordiv { vw }
  la lu labels om-put { sl }
  vw sl q!
  sa su intern sl 4 cells + s!
  0 sl 6 cells + !  1 sl 7 cells + !  rt sl 8 cells + ! ;

: import-file ( a u -- ok ) { fa fu }
  fa fu file-status nip if
    mb-reset s"  error - cannot open import file '" mb+ fa fu mb+ s" ': [Errno 2] No such file or directory: '" mb+ fa fu mb+ s" '" mb+ mb-get diag-e false exit
  then
  fa fu load-lines { tab n }
  0 imp-sec-n !
  n 0 ?do tab i tl@ split-tabs 3 >= if tab i tl@ imp-section-line then loop
  n 0 ?do tab i tl@ split-tabs 2 = if imp-label-line then loop
  true ;

\ ---- パス ----
10 om-new constant imported-labels
4 om-new constant pass1-final
6 om-new constant pcs-prev
variable pcs-prev-valid
65536 cells allocate throw constant hist-h
65536 cells allocate throw constant hist-i
variable hist-n
: hist-find ( h -- iter|0 ) { h }
  hist-n @ 0 ?do i cells hist-h + @ h = if i cells hist-i + @ unloop exit then loop 0 ;
: hist-add ( h iter -- ) hist-n @ 65536 >= if 2drop exit then
  hist-n @ cells hist-i + !  hist-n @ cells hist-h + !  1 hist-n +! ;

defer pass-reset-extra ( passno -- )
:noname drop ; is pass-reset-extra

: reset-for-pass ( -- )
  0 pc !  1 line-no !
  lw-default
  s" .text" cur-section!
  sections om-clear  0 nranges !
  vars-reset  true nsym-dirty ! ;

: finalize-section ( -- )
  cur-section sections om-find ?dup if
    { e } e 2 cells + @ { ep }
    pc @ ep - { blk }
    blk 0> if
      e cell+ dup @ blk + swap !
      cur-section ep blk range+
    then
  then ;

: lab-sec-str ( slot -- a u ) lab-sec ;
: label-undef-derived? ( slot -- f ) qundef-derived? ;

: pcs-hash ( -- h ) 0 { h }
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-key fnv { nh }
      i labels om-val { sl }
      sl @ { x } sl 1 cells + @ { x1 } sl 2 cells + @ { x2 } sl 3 cells + @ { x3 }
      sl lab-sec fnv { sh }
      h  nh x 11400714819323198485 * xor x1 3 * xor x2 5 * xor x3 7 * xor sh 13 * xor  + to h
    then
  loop
  h labels om-count xor ;

\ 前回の反復との比較
: count-moving ( -- n ) 0 { n }
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-key pcs-prev om-find { ps }
      i labels om-val { sl }
      sl qundef-derived? if n 1+ to n else
        ps 0= if n 1+ to n else sl ps q= 0= if n 1+ to n then then
      then
    then
  loop n ;

: has-undef? ( -- f )
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-val { sl }
      sl 6 cells + @ 0= sl qundef-derived? and if true unloop exit then
    then
  loop false ;

: save-relax-values ( -- )
  relax-prev om-clear
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-val { sl }
      sl qundef-derived? 0= if i labels om-key relax-prev om-put sl swap QB move then
    then
  loop ;
: save-pcs-prev ( -- )
  pcs-prev om-clear
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-key pcs-prev om-put { d }
      i labels om-val { sl }
      sl d QB move
      sl lab-sec d 4 cells + s!
    then
  loop ;

: abort-lines ( -- ) s"          Aborting: no output file written." etype ecr ;
: msg-force ( a u -- ) diag-wf ;

: changed-labels ( -- ) 0 { n }
  s"          Labels still changing: " etype
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-key pcs-prev om-find { ps }
      i labels om-val { sl }
      ps if
        sl ps q= 0= sl lab-sec ps 4 cells + s@ str=cs 0= or if
          n 10 < if
            n if s" , " etype then
            i labels om-key etype
          then
          n 1+ to n
        then
      then
    then
  loop
  ecr ;

: commit-macro-state ( -- )
  mlabel-vals om-clear
  relax-prev om-used 0 ?do
    i relax-prev om-live? if i relax-prev om-key mlabel-vals om-put  i relax-prev om-val swap QB move then
  loop
  true mlabels-valid !
  mline-pcs-prev om-clear
  mline-pcs-cur om-used 0 ?do
    i mline-pcs-cur om-live? if
      i mline-pcs-cur om-key mline-pcs-prev om-put { dst }
      i mline-pcs-cur om-val { src }
      src @ dst !  src cell+ @ dst cell+ !
    then
  loop ;

: run-pass1 ( a u -- ok ) { sa su }
  16 { budget }  -1 { minmv }  0 { it }
  pcs-prev-valid off  0 hist-n !
  pcs-prev om-clear  relax-prev om-clear
  begin it budget < while
    it 0= relax-optimistic !
    reset-for-pass
    mline-pcs-cur om-clear
    1 pass !
    labels om-clear  imported-labels labels om-copy
    1 pass-reset-extra
    ar-mark { mk }
    sa su fileassemble
    mk ar-release
    finalize-section
    pcs-prev-valid @ if
      count-moving { nm }
      nm 0<> minmv 0< nm minmv < or and if
        minmv 0>= if budget 1+ to budget  0 hist-n ! then
        nm to minmv
      then
    then
    has-undef? { hu }
    save-relax-values
    commit-macro-state
    hu 0= if
      pcs-hash { h }
      h hist-find { fs }
      fs 0<> if
        it 1+ fs - { cl }
        cl 1 = if
          opt-debug @ if mb-reset s" Pass1 relaxation converged after " mb+ it 1+ mb-n s"  iteration(s)" mb+ mb-get etype ecr then
          save-pcs-prev  true exit
        else
          mb-reset s"  error - Pass1 relaxation is oscillating with period " mb+ cl mb-n
          s"  (the instruction layout at iteration " mb+ it 1+ mb-n s"  is identical to iteration " mb+ fs mb-n
          s" ); it will never converge by simple repetition." mb+ mb-get msg-force
          abort-lines false exit
        then
      then
      h it 1+ hist-add
    then
    save-pcs-prev  true pcs-prev-valid !
    it 1+ to it
  repeat
  mb-reset s"  error - Pass1 relaxation did not converge after " mb+ budget mb-n s"  iterations." mb+ mb-get msg-force
  s"          Generated code would have incorrect addresses for" etype ecr
  s"          variable-length instructions with forward references." etype ecr
  abort-lines
  false ;

: pass1-capture ( -- )
  pass1-final om-clear
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-val { sl }
      sl 6 cells + @ 0= if i labels om-key pass1-final om-put sl swap QB move then
    then
  loop ;

: n>hex ( n -- a u ) base @ >r hex dup >r abs s>d <# #s r> sign #> r> base ! ;

: drift-report ( n -- ) { n }
  mb-reset s"  error - address mismatch between pass1 and pass2 (" mb+ n mb-n
  s"  label(s)); output addresses are UNRELIABLE." mb+ mb-get msg-force
  reported-lab-errs om-count 0> if
    s"          This is a consequence of the label definition error(s) reported above; fix those first." etype ecr
  else had-error @ if
    s"          This is a consequence of the error(s) reported above (a line in error emits nothing, so the addresses after it move); fix those first." etype ecr
  else
    s"          This usually means pass1 relaxation did not fully converge for variable-length forward references." etype ecr
  then then
  0 { shown }
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-val { sl }
      sl 6 cells + @ 0= if
        i labels om-key pass1-final om-find ?dup if
          { p1 }
          sl p1 q= 0= sl qundef-derived? 0= and if
            shown 10 < if
              s"            " etype i labels om-key etype
              s" : pass1=0x" etype p1 true q>hex etype s"  pass2=0x" etype sl true q>hex etype ecr
            then
            shown 1+ to shown
          then
        then
      then
    then
  loop
  shown 10 > if s"            ... and " etype shown 10 - .en s"  more." etype ecr then
  abort-lines ;

: count-drift ( -- n ) 0 { n }
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-val { sl }
      sl 6 cells + @ 0= if
        i labels om-key pass1-final om-find ?dup if
          sl swap q= 0= sl qundef-derived? 0= and if n 1+ to n then
        then
      then
    then
  loop n ;

: abort-assembly ( -- )
  s"  error - one or more errors were reported during assembly; output would be incomplete or wrong." diag-wf
  abort-lines ;

\ ---- -b のファイル ----
defer raw-zero-warn ( -- )                       \ -o と -b を同時に使ったときの警告
:noname ; is raw-zero-warn
variable fl-pos
: flush-raw ( -- )
  has-outfile @ 0= if exit then
  bts @ 0<= if
    mb-reset s"  error - flush: bts=" mb+ bts @ mb-n s"  is invalid (<=0); no output written to '" mb+ out-file-a @ out-file-u @ mb+ s" '." mb+ mb-get diag-e exit
  then
  omax @ 0= if exit then
  omax @ { nw }
  bts @ 7 + 8 / { bpw }
  nw bpw * { total }
  total 1073741824 > if
    mb-reset s"  error - output size " mb+ total mb-n s"  bytes exceeds maximum 1073741824. Check for incorrect .ORG or address values." mb+ mb-get diag-ef exit
  then
  total allocate throw { data }
  padding-v @ wmask and { pv }
  pv 0<> if
    nw 0 ?do
      bpw 0 ?do
        endian-big @ 0= if pv i 8 * rshift 255 and else pv bpw 1- i - 8 * rshift 255 and then
        data j bpw * i + + c!
      loop
    loop
  else data total erase then
  nw 0 ?do
    wset @ i + c@ if
      wbuf @ i cells + @ { v }
      bpw 0 ?do
        endian-big @ 0= if v i 8 * rshift 255 and else v bpw 1- i - 8 * rshift 255 and then
        data j bpw * i + + c!
      loop
    then
  loop
  out-file-a @ out-file-u @ w/o create-file if
    drop data free throw
    mb-reset s"  error - cannot write '" mb+ out-file-a @ out-file-u @ mb+ s" ': [Errno 2] No such file or directory: '" mb+ out-file-a @ out-file-u @ mb+ s" '" mb+ mb-get diag-e exit
  then
  { fid }
  data total fid write-file throw
  fid close-file throw
  data free throw
  mb-reset s" raw: wrote " mb+ out-file-a @ out-file-u @ mb+ s"  (" mb+ total mb-n s"  bytes)" mb+ mb-get etype ecr
  raw-zero-warn ;

\ ---- 出力 (-o と -e/-E) の口 ----
defer write-elf-obj ( -- )
:noname ; is write-elf-obj
defer write-exports ( -- ok )
:noname true ; is write-exports
defer elf-desc-out ( -- )
:noname ; is elf-desc-out
defer register-elfdecls ( -- )
:noname ; is register-elfdecls
defer macro-expand-only ( fa fu dest-a dest-u pat? -- ok )
:noname 2drop 2drop drop false ; is macro-expand-only
defer apply-elf-options ( -- ok )
:noname true ; is apply-elf-options

: pass2 ( a u -- ) { sa su }
  reset-for-pass
  2 pass !
  2 pass-reset-extra
  sa su fileassemble
  finalize-section ;

\ ---- 対話モード ----
create inbuf 1024 allot
: print-labels ( -- )
  \ ラベルを名前順に標準エラーへ
  labels om-used 0 ?do
    i labels om-live? if
      i labels om-key etype
    then
  loop ;

: interactive ( -- )
  0 pc !  0 pass !  1 line-no !  s" (stdin)" file!
  begin
    pc @ 16 hexw s" : " type
    s" >> " type
    inbuf 1024 stdin read-line throw
  while
    inbuf swap trim
    dup 0= if 2drop else
      2dup s" ?" str=cs if 2drop print-labels else lineassemble0 drop then
    then
  repeat drop ;

: prep-pattern ( -- ok )
  o-pat-a @ o-pat-u @ read-pattern
  build-pat-index
  unordered-plan
  nrows @ 0 ?do loop
  had-error @ if
    s"  error - one or more errors were reported during assembly; output would be incomplete or wrong." diag-wf
    s"          Aborting: no output file written." etype ecr false exit
  then
  set-pat-symbols
  register-elfdecls
  had-error @ if
    s"  error - one or more errors were reported while reading the pattern file; output would be incomplete or wrong." diag-wf
    s"          Aborting: no output file written." etype ecr false exit
  then
  true ;

: run ( -- ok )
  collect-args
  av-n @ 0= if help-text type true exit then
  0 begin dup av-n @ < while parse-opt repeat drop
  o-help @ if help-text type true exit then
  o-npos @ 0= if s" the following arguments are required: patternfile" arg-error then
  o-osabi-a @ o-osabi-u @ slower { oa ou }
  oa ou s" linux" str=cs 0= oa ou s" freebsd" str=cs 0= and if
    s" warning: unknown --osabi value '" etype o-osabi-a @ o-osabi-u @ etype
    s" '; valid choices are ['linux', 'freebsd'] (case-insensitive). Using 'Linux'." etype ecr
  then
  apply-elf-options 0= if false exit then
  o-nomacro @ if 0 mp-src mp.enabled + ! 0 mp-pat mp.enabled + ! then
  o-mp? @ if o-pat-a @ o-pat-u @ o-mp-a @ o-mp-u @ true macro-expand-only exit then
  o-mx? @ if
    o-src? @ 0= if s"  error - -P/--macro-expand needs a source file." diag-wf false exit then
    o-src-a @ o-src-u @ o-mx-a @ o-mx-u @ false macro-expand-only exit
  then
  err-init
  0 pass !
  prep-pattern 0= if false exit then
  o-elfdesc @ if elf-desc-out true exit then
  o-imp-u @ if
    o-imp-a @ o-imp-u @ import-file 0= if false exit then
  then
  labels imported-labels om-copy
  o-src? @ 0= if interactive
  else
    o-src-a @ o-src-u @ run-pass1 0= if false exit then
    false relax-optimistic !
    pass1-capture
    o-src-a @ o-src-u @ pass2
    count-drift ?dup if drift-report false exit then
    had-error @ if abort-assembly false exit then
  then
  flush-raw
  had-error @ if false exit then
  write-elf-obj
  had-error @ if abort-assembly false exit then
  o-expe-u @ 0<> o-exp-u @ 0<> and if
    s" warning: both -e '" etype o-exp-a @ o-exp-u @ etype s" ' and -E '" etype o-expe-a @ o-expe-u @ etype
    s" ' specified; exporting plain format to -e and ELF format to -E separately." etype ecr
  then
  write-exports ;

\ 標準出力へ書けなかったか (caxx.c の最後の fflush と同じ報告)
: stdout-ok? ( -- f )
  stdout flush-file dup 0= if drop true exit then
  512 + negate { en }
  mb-reset s"  error - cannot write to standard output: [Errno " mb+ en mb-n s" ] " mb+ en errno-text mb+
  mb-get etype ecr false ;
: main ( -- )
  wbuf-init  pend-init  err-init  opts-init
  run stdout-ok? and if 0 else 1 then (bye) ;
