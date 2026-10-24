\ vars.fs -- パターン変数の束縛 (caxx.c の PatVar / var_slot)
\
\ 名前は小文字で正規化して番号 (slot) を振る。値・未定義印・浮動小数点印・
\ 写し取った綴りを slot ごとに持つ。束縛はパターン 1 行 (1 候補) ごとに消す。

decimal

256 constant NVARS
2 om-new constant vname-map            \ 名前 -> slot (value[0])
1 om-new constant varnames            \ 使われた変数名 (.exp の検査用)
create vname-a NVARS cells allot       \ slot -> 名前
create vname-u NVARS cells allot
variable nvslots

create vq    NVARS QB * allot
create vund  NVARS cells allot
create vflt  NVARS cells allot
create vset  NVARS cells allot         \ この候補で束縛されたか
create vta   NVARS cells allot         \ 写し取った綴り
create vtu   NVARS cells allot
create vtouch NVARS cells allot        \ 触った slot の一覧
variable ntouch

create sq    NVARS QB * allot          \ 最良候補の写し
create sund  NVARS cells allot
create sflt  NVARS cells allot
create sset  NVARS cells allot
create sta   NVARS cells allot
create stu   NVARS cells allot
create stouch NVARS cells allot
variable nstouch

: var-name? ( a u -- f ) { a u }                \ 小文字にして: [a-z][a-z0-9_]*
  u 0= if false exit then
  a c@ lc lowc? 0= if false exit then
  u 1 ?do a i + c@ lc dup lowc? over digc? or swap 95 = or 0= if false unloop exit then loop
  true ;

: vslot ( a u create? -- slot|-1 ) { a u cr }
  a u var-name? 0= if -1 exit then
  a u slower { la lu }
  la lu vname-map om-find ?dup if @ exit then
  cr 0= if -1 exit then
  la lu varnames om-put drop
  nvslots @ NVARS >= if
    s"  error - too many pattern variable names (maximum 256)." etype ecr -1 exit
  then
  la lu vname-map om-put nvslots @ swap !
  la lu hdup nvslots @ cells vname-u + !  nvslots @ cells vname-a + !
  nvslots @  1 nvslots +! ;
: vslot-name ( slot -- a u ) dup cells vname-a + @ swap cells vname-u + @ ;

: vtouched ( slot -- ) { sl }
  sl cells vset + @ 0= if
    true sl cells vset + !
    sl ntouch @ cells vtouch + !  1 ntouch +!
  then ;
: vars-reset ( -- )
  ntouch @ 0 ?do
    i cells vtouch + @ { sl }
    false sl cells vset + !  false sl cells vund + !  false sl cells vflt + !
    0 sl cells vta + !  0 sl cells vtu + !
    sl QB * vq + QB erase
  loop
  0 ntouch ! ;
: var-bound? ( slot -- f ) cells vset + @ ;

\ 値を書く。is-float は書いた時点の式のモード。
: vput ( slot q undef? float? -- ) { sl q un fl }
  sl 0< if exit then
  sl vtouched
  q sl QB * vq + QB move
  un sl cells vund + !  fl sl cells vflt + ! ;
: vput-text ( slot a u -- ) { sl a u }
  sl 0< if exit then
  sl vtouched
  a sl cells vta + !  u sl cells vtu + ! ;
: vtext ( slot -- a u ) { sl } sl 0< if 0 0 exit then sl cells vta + @ sl cells vtu + @ ;
: vval ( slot -- q ) dup 0< if drop q0 exit then QB * vq + ;
: vundef? ( slot -- f ) dup 0< if drop false exit then cells vund + @ ;
: vfloat? ( slot -- f ) dup 0< if drop false exit then cells vflt + @ ;

\ 最良候補の保存・復元
: vsave ( -- )
  ntouch @ nstouch !
  ntouch @ 0 ?do
    i cells vtouch + @ { sl }
    sl i cells stouch + !
    sl QB * vq + sl QB * sq + QB move
    sl cells vund + @ sl cells sund + !
    sl cells vflt + @ sl cells sflt + !
    sl cells vta + @ sl cells sta + !
    sl cells vtu + @ sl cells stu + !
  loop ;
: vrestore ( -- )
  vars-reset
  nstouch @ 0 ?do
    i cells stouch + @ { sl }
    sl vtouched
    sl QB * sq + sl QB * vq + QB move
    sl cells sund + @ sl cells vund + !
    sl cells sflt + @ sl cells vflt + !
    sl cells sta + @ sl cells vta + !
    sl cells stu + @ sl cells vtu + !
  loop ;

\ -o の追跡の状態 (照合から参照するのでここに置く)
variable trk-on     false trk-on !
variable trk-widx   -1 trk-widx !
variable trk-cap    -1 trk-cap !
defer elf-cap-finish ( slot a u -- )               \ 変数の取り込みが終わったところ
:noname 2drop drop ; is elf-cap-finish
defer trk-push ( -- )
:noname ; is trk-push
defer trk-top-restore ( -- )
:noname ; is trk-top-restore
defer trk-pop ( -- )
:noname ; is trk-pop
defer trk-cand-begin ( -- )
:noname ; is trk-cand-begin
defer trk-cand-best ( -- )
:noname ; is trk-cand-best
defer trk-cand-restore ( -- )
:noname ; is trk-cand-restore
defer trk-best-install ( -- )
:noname ; is trk-best-install
defer trk-probe-begin ( -- )
:noname ; is trk-probe-begin
defer trk-probe-end ( -- )
:noname ; is trk-probe-end
defer elf-call-drop ( w -- )
:noname drop ; is elf-call-drop
