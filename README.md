# axx

general purpose assembler axx

GENERAL PURPOSE ASSEMBLER 'axx.py'

axx.pyはアセンブラを一般化したジェネラルパーパス（汎用）・アセンブラです。

拙作のexpression.pyモジュールを使っています。



・使い方

axx.py 8048.axx [ sample.asm ]のように使います。

axxは第1引数から、アセンブラのパターンデータを読み込み、パターンデータに基づき第2引数のソースファイルをアセンブルします。

第2引数を省略したら、標準入力からソースを入力します。

・パターンデータの解説

パターンデータは、

'command' 'operands' 'error_pattern' 'object_list'

のように並んでいて、commandをスペースにして省略すると直前のcommandが採用されます。

'command'はスペースにする以外は必ず指定しなければなりません。operandsはない場合があります。object_listは必ず指定しなければなりません。error_patternは省略可なので、パターンデータの種類は、

(1) command object_list

(2) command operands object_list

(3) command operands error_pattern object_list

の3種類になります。

・コメント

パターンファイル内に、'//'を書くとその行の//以降がコメントになります。

・大文字・小文字の別、変数

パターンファイルのcommandは大文字で書いてください。operandsの定数文字も大文字にしてください。

アセンブルラインからは、大文字でも小文字でも同じとして受け付けます。

operandsとerror_patternとobject_listの小文字のアルファベットは変数です。

小文字のアルファベットにoperandsのその位置に当たる数値やシンボルの値が変数に代入されます。小文字のaからnは定数、oからyはシンボルを表します。error_patternとobject_listで変数を参照します。

特殊な変数はzで、現在のロケーションカウンタを表します。オブジェクトが生成されるごとに、ロケーションカウンタはその値を増やします。

・error_pattern

error_patternは、変数と比較演算子を使い、エラーの出る条件を指定します。

error_patternは複数指定可で、','で区切って入力します。

例えば、以下のようです。

a>3;4,b>7;5

この例では、a>3のとき、エラーコード4を返し、b>7のときエラーコード5を返します。

・object_list

object_listは、出力するコードを','で区切って指定します。例えば、0x03,dとすると、0x3の次にdが格納されます。

8048を例に取ってみると、

ADD A,Rn n>7;5 n|0x68

では、ADD A,Rnとすると、n>7のときエラーコード5を返し、n|0x68のオブジェクトが生成されます。例えば、上記のラインがあると、add a,r1は0x69というオブジェクトを出力します。

・symbol

パターンファイル内に

$symbol=n

と書くと、symbolが値nで定義されます。

z80の例を挙げます。

パターンファイル内に

$B=0

$C=1

$D=2

$E=3

$H=5

$L=6

$A=7

$BC=0x00

$DE=0x10

$HL=0x20

$SP=0x30

と書いておくと、シンボルB,C,D,E,H,L,A,BC,DE,HL,SPを、それぞれ0,1,2,3,4,5,6,7,0x00,0x10,0x20,0x30として定義します。シンボルには、大文字小文字の区別はありません。

パターンファイル中に同じシンボルの定義が複数あると、新しいものが古いものを更新します。すなわち、

$B=0

$C=1

ADD A,s

$NZ=0

$Z=1

$NC=2

$C=3

RET s

とあると、ADD A,CのCは0、RET CのCは3になります。

・オブジェクト出力の例

LD s,d (s&0xf!=0)||(s>>4)>3;9 s|0x01,d&0xff,d>>8

で、ld bc,0x1234, ld de,0x1234, ld hl,0x1234が、それぞれ、0x01,0x34,0x12、0x11,0x34,0x12、0x21,0x34,0x12を出力します。

・ニモニックの順番

(1) LD A,(HL)

(2) LD A,d

のように、パターンファイルは上から順に評価されますので、先に置かれたほうが優先します。

この場合、(1)と(2)が逆だと、アセンブルラインのld a,(hl)は、dの値に(hl)を入れることになってしまうので、パターンファイルのLD A,(HL)はLD A,dより先に置いてください。特殊なパターンを先に、一般のパターンを後に置きます。

・エラーチェック

エラーチェックが甘いです。
