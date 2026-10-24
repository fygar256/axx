\ match3.fs -- 照合 (続き): [[ ]] の組み合わせと .sub の展開

decimal

create gop 24 cells allot
create gcl 24 cells allot
create gstk 24 cells allot
sb-new constant tb
: find-groups ( a u -- ) { a u } 0 0 0 0 { k serial sp ser }
  begin k 1+ u < while
    a u k 91 91 at2? if
      serial 1+ to serial
      serial 24 < if
        k gop serial cells + !
        serial gstk sp cells + !  sp 1+ to sp
      then
      k 2 + to k
    else
      a u k 93 93 at2? if
        sp 0> if
          sp 1- to sp  gstk sp cells + @ to ser
          k gcl ser cells + !
        then
        k 2 + to k
      else k 1+ to k then
    then
  repeat ;
: build-text ( a u mask cnt -- a' u' ) { a u mask cnt } 0 0 { k rm }
  tb sb-clear
  begin k u < while
    false to rm
    cnt 1+ 1 ?do
      mask 1 cnt i - lshift and if
        gop i cells + @ k <= gcl i cells + @ 1+ k >= and if true to rm then
      then
    loop
    rm if k 1+ to k else
      a u k 91 91 at2? if k 2 + to k else
      a u k 93 93 at2? if 32 tb sb-c k 2 + to k else
      a k + c@ tb sb-c k 1+ to k then then
    then
  repeat
  tb sb$ ;
: popcnt ( n -- k ) 0 swap begin dup while dup 1 and rot + swap 1 rshift repeat drop ;

: match-groups ( a u cnt -- flag ) { a u cnt } 0 0 { pop mask }
  cnt 20 > if 20 to cnt then
  a u find-groups
  cnt 1+ 0 ?do
    i to pop
    1 cnt lshift 1- to mask
    begin mask 0>= while
      mask popcnt pop = if
        a u mask cnt build-text mt-u ! mt-a !
        vars-reset
        match1 if true unloop exit then
      then
      mask 1- to mask
    repeat
  loop
  false ;

: has-brackets? ( a u -- n f )                    \ [[ の数, [[ または ]] があるか
  2dup count-sub { n } 2dup s" ]]" search nip nip { cl } s" [[" search nip nip n 0> or cl or n swap ;
: match-text ( a u -- flag ) { a u }
  a u has-brackets? if
    a u rot match-groups
  else
    drop a mt-a ! u mt-u !  vars-reset  match1
  then ;

