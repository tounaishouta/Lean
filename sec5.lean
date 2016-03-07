import standard
import data.tuple

/-

5. Intteracting with Lean

5章では、いくつかの実際的な Lean の使い方を学びます。

5.1 Display Infromation

5.1節では、現在の状況や objects に関する情報を
表示する方法を学びます。

-/

-- print <識別子>
-- <識別子> の情報を表示する。
-- 種類、型、定義など
print nat
print add
print definition add -- 違いはよく分からない。
print +

-- check <式>
-- <式> の型を表示する。
-- @ と組合せると効果的
check nat
check add
check @add
check 3 + 2

-- eval <式>
-- <式> を評価した結果を表示する。
eval (λ x : ℕ, x + 2) 3
eval 2 + 3
eval 2 + (3 : ℕ)

-- 他にもたくさん
/-
print notation
print notation + * -
print axioms
print options
print prefix nat -- 便利かも
print prefix nat.le
print coercions
print coercions num
print classes
print instances ring
print fields ring
-/

-- 定理などを検索する。
-- find_decl <パターン>
-- find_decl <パターン>, + <文字列> : <文字列> を含む
-- find_decl <パターン>, - <文字列> : <文字列> を含まない

-- 例
/-
find_decl (_ - _) * _ = _ * _ - _ * _
find_decl _ * (_ + _) = _ * _ + _ * _
find_decl _ - (_ + _) = _ - _ - _
find_decl _ + _ - _ = _ + (_ - _), + assoc
find_decl _ - _ = 0
find_decl _ + 0 = _
-/

example (A : Type) (s : comm_ring A) (x y : A) :
  (x - y) * (x + y) = x * x - y * y :=
calc
  (x - y) * (x + y)
      = x * (x + y) - y * (x + y)       : mul_sub_right_distrib
  ... = x * x + x * y - y * (x + y)     : left_distrib
  ... = x * x + x * y - (y * x + y * y) : left_distrib
  ... = x * x + x * y - y * x - y * y   : sub_add_eq_sub_sub
  ... = x * x + (x * y - y * x) - y * y : add_sub_assoc
  ... = x * x + (x * y - x * y) - y * y : mul.comm
  ... = x * x + 0 - y * y               : sub_self
  ... = x * x - y * y                   : add_zero

/-

5.2 Setting Options

Lean のオプションを設定できます。方法は

set_option <オプション名> <値>

表示の仕方を制御するオプションなどがあります。

-/

/-

5.3 Using the Library

** import は推移的に行われます。

foo の中で
  import bar
されているならば、
作業中のファイルで
  import foo
すれば、
  import bar
する必要はありません。

** open した内容は引き継がれません。

foo の中で
  open bar
されていて、
作業中のファイルで
  import foo
しても、bar の内容は open されません。

** Library の構造は GitHub で

https://gihtub.com/leanprover/lean/tree/master/library

markdown ファイル（拡張子が .md のもの）に
概要が書かれているので
それを見るのが楽

** 命名規則

ライブラリの命名規則を理解しておくと、
（あとでやる Tab 補完と合わせて）
定理などを見つけやすい。

-/

/-

5.4 Lean's Emacs Mode

インストールは各自頑張ってください。
(Ubuntu が楽ですよ!!)

Emacs の使い方
* 普通のエディタとして直感的に操作できます（できるはずです）
* ショートカットを覚えると捗ります。

C-a : Ctrl を押しながら a
      Ctrl を多用するので、a の左などに割りあてておくと楽
      (Ctrl2cap で検索)
M-a : Alt (Option) を押しながら a,
      または、Esc を押して離してから a
      あるいは C-[ してから a

例
C-x C-f : (新しい)ファイルを開く (file, find) (Ctrl を押したまま x f)
C-x C-s : 保存 (save)
C-x C-c : Emacs を終了する (close)
C-x u   : 元に戻す (undo)
C-x b   : バッファ切り替え (buffer)
C-x 0   : 現在のウィンドウを閉じる
C-x 1   : 他のウィンドウを閉じる
C-x 2   : 上下に分割
C-x 3   : 左右に分割
C-x o   : ウィンドウを移動
C-y     : ペースト (yank)
C-n     : 下 (next)
C-p     : 上 (previous)
C-f     : 右 (forward)
C-b     : 左 (backward)
C-a     : 行頭へ (?)
C-e     : 行末へ (end)
C-/     : undo

C-c ... : Lean 関係

Emacs のメリット
* ファイルに保存できる! (拡張子は .lean)
* 速い！ リアルタイム！

注意: tutorial の内容をコピペして使う場合、
適宜 import や open を補う必要があります。

エラーがある箇所は波線が引かれます。
C-c ! ... : エラー関係
C-c ! l   : エラーリストを表示 (list)
C-c ! n   : 次のエラー箇所へ (next)
C-c ! p   : 前のエラー箇所へ (previous)

カーソルを合わせた識別子の型が文脈を反映して下端に表示されます。
開き括弧にカーソルを合わせると括弧全体の型を表示します。
-/
check λ x y, x = y
check λ x y : ℕ, x = y
/-

アンダースコアで省略した内容を補完できます。
C-c C-f : アンダースコアを推論した結果で置換

-/

example (p totemonagainamaenomeidai : Prop) : p → (p → totemonagainamaenomeidai) → totemonagainamaenomeidai :=
assume Hp : p,
assume H : _,
show _, from H Hp

/-

アンダースコアや sorry を上手く使って
先に証明の骨格を書くのが楽 (?)

Tab 補完できます! (超絶便利!!!)
識別子を途中まで入力して tab を押すと、
該当する名前の識別子を型と一緒に列挙してくれます。
一番上に入力したいものがあれば Enter で確定
矢印キーで選択もできます。

その場で print
C-c C-p : カーソル上の識別子を print

定義元を参照
M-. : カーソル上の識別子が定義されている箇所へジャンプ
M-* : 作業中の箇所へ戻る

入力の仕方を表示
C-c C-k : カーソルの上の記号の入力法を表示

その他
C-c C-o : オプションを設定
C-c C-e : コマンドを実行
C-c C-r : プロセスを再起動

ファイルの読みこみを途中で止める
ファイルの途中に exit と書いておくと、
Lean はそれより後を無視する。
長いファイルを編集する際、
途中でエラーがたくさんでるのを一時的に無視したいときなど (?)

-/

/-

5.5 Projects

自分で書いた .lean ファイルを他の .lean ファイルから import するには、
オブジェクト (.olean) ファイルを生成する必要がある。
(プログラミング言語のコンパイルに対応)

-- ここから読み飛ばして ok

例えば、hogehoge.lean の内容を import したい場合は,
シェルから
  lean -o hogehoge.olean hogehoge.lean
とすれば、（エラーがなければ) hogehoge.olean ファイルが生成され
他の .lean ファイルから
  import hogehoge
で読み込むことができる(とりあえず同じフォルダにある場合)。

でもこれは面倒なので、もっと楽なやりかたを後で

-- ここまで

import が参照する箇所

  import hogehoge
とした場合、Lean はデフォルトでは次の場所から hogehoge.olean を探します。
* standard library のルート
  https://github.com/leanprover/lean/tree/master/library
* そのファイルがあるフォルダ

(import standard は library 直下の
standard.olean を参照していたわけです。)

ピリオド (.) を使って階層構造を表します。
  import hogehoge.fugafuga
とした場合は、上の二箇所からフォルダから
 hogehoge の中の fugafuga.olean を探します。
より階層が深くなっても同様です。e.g.
  import hogehoge.fugafuga.piyopiyo

(import data.nat は library 直下のフォルダ data の中の
nat.olean を参照していたわけです。
と思ったけど、data/nat.olean は存在しないので、
フォルダ名を指定した場合は、data/nat/ の中の .olean ファイル全てを
読みこむのかもしれない。分からない。)

先頭にピリオドをつけると、そのファイルがあるフォルダを探します。e.g.
  import .hogehoge
  import .hogehoge.fugafuga
ピリオド二つ (..) で階層を遡ります。e.g.
  import ..hogehoge
  import ..hogehoge.fugafuga

プロジェクトについて

プロジェクトを用いて複数の .lean ファイルを伴う作業を快適に
行えます。

実演する。
* hogehoge.lean を作成する。
* メニュー Lean から Create a new project を実行
* hogehoge.lean が存在するフォルダを選択
* これ以降、このフォルダの中に保存された .lean ファイル
  (階層的でも OK) はこのプロジェクトに管理される。
* このフォルダに fugafuga.lean を作成し、
* piyopiyo を定義。
* fugafuga.lean を保存 (←多分必要)
* hogehoge から import fugafuga して piyopiyo を使用できる。

プロジェクト全体をコンパイルするには、
そのフォルダ内のどこかでシェルから
  linja
すればOK

-/

/-

5.6 Notation and Abbreviations

-/

namespace sec5_6

open nat

notation `[` a `**` b `]` := a * b + (1 : ℕ)
infix `<*>`:50 := λ x y : ℕ, x * x * y * y

print notation [
print notation <*>

eval [2 ** 3]
eval 2 <*> 3

end sec5_6

/-

5.7 Coercions

-/

namespace sec5_7

open bool nat int

print coercions

definition hogehoge [coercion] (b : bool) : ℕ :=
bool.rec_on b 0 1

print prefix bool

set_option pp.coercions true

print coercions
print sec5_7._trans_of_hogehoge

eval 2 + tt
eval (2 : ℤ) + tt

end sec5_7
