import standard

namespace chapter8
/-

Chapter 8. Building Theories and Proofs

実際的な Lean の機能について議論します。

Section 8.1. More on Coercions

前回、議論した coercion についてより詳しい説明をします。
まずは coercion の復習
-/
namespace coercion0

-- 現在定義されている coercion を確認する。
print coercions
-- num ↣ int : int.of_num

open bool nat

-- 新しく定義する関数に coercion attribute を付与する。
definition foo [coercion] : bool → nat
| foo ff := 0
| foo tt := 1

-- 既に定義された関数に coercion attribute を付与する。
attribute int.of_nat [coercion]
-- local attribute int.of_nat [coercion] -- local にもできる。

print coercions
-- num ↣ int : int.of_num
-- bool ↣ int : int._trans_to_of_nat
-- bool ↣ nat : foo
-- nat ↣ int : int.of_nat

-- int が必要なところに bool を与えると coercion で変換される。
eval (ff : int) --> 0
eval (tt : int) --> 1

-- coercion は推移的に生成される。（命名規則はよくわからない）
-- 適用可能な coercion が複数ある場合は最も新しく定義されたものが使われる？

-- coercion は attribute が付与された namespace で有効
-- その namespace を open した後も有効
-- local attribute ... を使うと付与した namespace で有効だが
-- open しても有効にならない。

-- pp.coercions オプションにより print されるメッセージに
-- coercion を明示的に表示させることができる。

check (ff : nat) --> ff : ℕ

set_option pp.coercions true

check (ff : nat) --> foo ff : ℕ

end coercion0
/-
今回の話

coercion attribute を付与できるのは次の型を持つ項に対してだけ

1. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), D t_1 ... t_m
2. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), Type
3. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), (Pi x : A, B x)

個別に見ていこう。

1. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), D t_1 ... t_m
   i.e パラメータを持つ型 C からパラメータを持つ型 D へ
       （t_1, ..., t_m は x_1, ..., x_n, y に依存してよい。）

例 C := list, D := set のとき
-/
namespace coercion1

open list

print list
print set --> : Type → Type := λ (X : Type), X → Prop

definition contains {A : Type} : list A → A → Prop
| contains nil       _ := false
| contains (x :: xs) y := x = y ∨ contains xs y

definition set_of_list [coercion] {A : Type} : list A → set A := contains

check λ (A : Type) (xs : set A) (y : A), xs y            --> OK
check λ (A : Type) (xs : list A) (y : A), xs y           --> Error!
check λ (A : Type) (xs : list A) (y : A), (xs : set A) y --> OK (use set_of_list)

-- 次の話
attribute contains [coercion]
check λ (A : Type) (xs : list A) (y : A), xs y           --> OK (use contains)

end coercion1
/-

2. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), Type
   i.e. パラメータを持つ型 C から Type へ

例 C := Semigroup
-/
namespace coercion2

structure Semigroup :=
  (carrier : Type) -- underlying set に相当
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

check Semigroup.carrier --> : Semigroup → Type
attribute Semigroup.carrier [coercion]

notation a `*` b := Semigroup.mul _ a b

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  calc (a * b) * c = a * (b * c) : Semigroup.mul_assoc
-- coercion により ... (a b c : Semigroup.carrier S) ... に変換される。
-- 数学で代数構造などを持った対象 (S, *) と underlying set S を同じ記号で表す感覚

end coercion2
/-

3. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), (Pi x : A, B x)
   i.e. パラメータを持つ型 C から関数型へ
        A, B は x1, ..., x_n, y に依存してよい。

例 C := Semigroup.morphism, A := S1, B x := S2
-/
namespace coercion3

open coercion2

structure morphism (S1 S2 : Semigroup) :=
  (mor : S1 → S2)
  -- coercion により (mor : Semigroup.carrier S1 → Semigroup.carrier S2) に
  (resp_mul : ∀ a b : S1, mor (a * b) = mor a * mor b)
  -- 上にも coercion が隠れています。

check @morphism.mor --> Π {S1 : Semigroup} {S2 : Semigroup},  morphism S1 S2 → S1 → S2
attribute morphism.mor [coercion]

example (S1 S2 : Semigroup) (f : morphism S1 S2) (a b : S1) :
  f (a * b) = f a * f b :=
  calc f (a * b) = f a * f b : morphism.resp_mul
-- f は structure だが”写像”として扱える。

end coercion3
/-
--------------------------------------------------------------------------------

Section 8.2. More on Implicit Argument

復習しながら見ていく。
-/
namespace implicit1

open bool nat

definition foo {A : Type} : A → A
| foo a := a

-- brace { } で囲むと implicit argument になる。
-- λ {...}, ... や variable {...} の形でも

check foo
check @foo -- foo の explicit version
check @foo _ -- foo は”常に” @foo _ に展開される。
check foo ff -- は
check @foo _ ff -- に展開されて
check @foo bool ff -- underscore は bool に substitute される。

check nat.mul_assoc
check !nat.mul_assoc -- は
check nat.mul_assoc _ _ _ -- に展開される。
-- アンダースコアは次の引数が残りの引数と結果の型から推論される限り
-- つけ加えられる。
-- 特に、補完されるアンダースコアの数は ! をつけた対象の型だけできまり、
-- 文脈によらない。

definition T (A B : Type) (a : A) (b : B) : Type := sorry

check !T -- T _ _ に展開される。
-- 第３、第４の引数の型から第１、第２引数は推論される。

definition t (A B : Type) (a : A) (b : B) : T A B a b := sorry

check !t -- t _ _ _ _ に展開される。
-- 結果の型から全ての引数が推論される。

-- variable を使う場合、途中から implicit にできる。
section

variable A : Type
variable a : A

definition baz : A := a

variable {A}

definition qux : A := a

end

check baz
check qux

end implicit1

namespace implicit2

variables {A : Type} (R : A → A → Prop)

definition reflexive  : Prop := ∀ (a : A), R a a
definition symmetric  : Prop := ∀ {a b : A}, R a b → R b a
definition transitive : Prop := ∀ {a b c : A}, R a b → R b c → R a c
definition euclidean  : Prop := ∀ {a b c : A}, R a b → R a c → R b c

check @reflexive  --> Π {A : Type} (A → A → Prop) → Prop
check @symmetric  --> Π {A : Type} (A → A → Prop) → Prop
check @transitive --> Π {A : Type} (A → A → Prop) → Prop
check @euclidean  --> Π {A : Type} (A → A → Prop) → Prop

variable {R}

theorem th1 (refl : reflexive R) (eucl : euclidean R) : symmetric R :=
  take a b : A,
  suppose R a b,
  have R a a, from !refl,
  show R b a, from eucl `R a b` `R a a`

check @th1
-- ∀ {A : Type} {R : A → A → Prop}, reflexive R → euclidean R → symmetric R

theorem th2 (symm : symmetric R) (eucl : euclidean R) : transitive R :=
  take a b c : A,
  suppose R a b,
  suppose R b c,
  have R b a, from symm `R a b`,
  show R a c, from eucl `R b a` `R b c`

check @th2
-- ∀ {A : Type} {R : A → A → Prop}, symmetric R → euclidean R → transitive R

theorem th3 (refl : reflexive R) (eucl : euclidean R) : transitive R :=
  -- th2 (th1 refl eucl) eucl
  -- Error!
/-
type mismatch at application
  th1 refl eucl
term
  eucl
has type
  R ?M_2 ?M_3 → R ?M_2 ?M_4 → R ?M_3 ?M_4
but is expected to have type
  euclidean ?M_1
-/
  -- @(th2 @(th1 refl @eucl) @eucl)
  -- あるいは、
  @th2 _ _ (@th1 _ _ @refl @eucl) @eucl

end implicit2
/-

implicit argument を持つ関数を引数として渡したときに、
@eucl _ _ _ のように 展開されてしまい、上手くいかない。

このような問題を解決するのに便利なのが
weaker implicit argument

⦃ と ⦄ (\{{ \}} で入力) あるいは {{ }}で囲むことで
weaker implicit argument になる。
wekar implicit argument を持つ関数 t は、
関数として使用した（関数適用の左側に来た）ときのみ、
@t _ の形に展開されるが、
それ以外のときは @t のまま

先程の例を weaker implicit argument で書き直してみる。
-/

namespace implicit3

variables {A : Type} (R : A → A → Prop)

definition reflexive  : Prop := ∀ (a : A), R a a
definition symmetric  : Prop := ∀ ⦃a b : A⦄, R a b → R b a
definition transitive : Prop := ∀ ⦃a b c : A⦄, R a b → R b c → R a c
definition euclidean  : Prop := ∀ ⦃a b c : A⦄, R a b → R a c → R b c

check @reflexive  --> Π {A : Type} (A → A → Prop) → Prop
check @symmetric  --> Π {A : Type} (A → A → Prop) → Prop
check @transitive --> Π {A : Type} (A → A → Prop) → Prop
check @euclidean  --> Π {A : Type} (A → A → Prop) → Prop

variable {R}

theorem th1 (refl : reflexive R) (eucl : euclidean R) : symmetric R :=
  take a b : A,
  suppose R a b,
  have R a a, from !refl,
  show R b a, from eucl `R a b` `R a a`

check @th1
-- ∀ {A : Type} {R : A → A → Prop}, reflexive R → euclidean R → symmetric R

theorem th2 (symm : symmetric R) (eucl : euclidean R) : transitive R :=
  take a b c : A,
  suppose R a b,
  suppose R b c,
  have R b a, from symm `R a b`,
  show R a c, from eucl `R b a` `R b c`

check @th2
-- ∀ {A : Type} {R : A → A → Prop}, symmetric R → euclidean R → transitive R

theorem th3 (refl : reflexive R) (eucl : euclidean R) : transitive R :=
  th2 (th1 refl eucl) eucl

end implicit3
/-
まとめ（と次回予告）

引数には次の４種類ある。

1. explicit argument (a : A) or a : A
   明示的に引数を与える必要がある。

2. implicit argument {a : A}
   @t _ の形に展開される。

3. wekaer implicit argument ⦃a : A⦄ or {{a : A}}
   関数として使用したときのみ @t _ の形に展開される。

4. Type Class に関するもの [a : A]
   次の章で扱う。

--------------------------------------------------------------------------------

Section 8.3 Elaboration and Unification

λ x y z, f (x + y) z のような "不完全" な式を受け取り
implicit な情報を推論する処理を elaboration という？

implicit な情報には
* 省略された型
* overload された notation の内どれを採用するか
  （どのように parse するか？）
* implicit argument を何で埋めるか
* どこにどの coercion を適用するか
などがある。

結論からいうと Lean の elaboration algorithm は
o powerful
x subtle
x complex
x not complete
x potentially nonterminating
o performs  quite well in ordinary situations
らしい。

* elaborator が省略した情報をどれくらい確実に推論できるか
* error message にどのように対応すべきか
を知るためにこのあたりの理解が必要？
（この節だけ読んでもいまいち分かりませんでしたが。。。）

以下、Lean の elaboration プロセスを順を追って説明する。

1. implicit argument のための "hole" を挿入する。

先程の節でみたように、
t : Π {a : A}, T a
のとき、t は @t _ に置き換えられる。

2. instantiate metavariables

入力された _ や上のステップで付け加えられた _ に
メタ変数 ?M1, ?M2, ... を割り当てる。
（error message でたまに出る ?M1 みたいなのはここで付与されたもの）

3. overload された（複数の意味を持つ）notation e.g.
   -/
   namespace elaboration0
   open sum
   print notation +
   -- print result:
   -- _ `+`:65 _:65 :=
   --   | add #1 #0
   --   | sum #1 #0
   end elaboration0
   /-
   についてありうる解釈を列挙する。
   （notation の parse の問題もここで？）

4. coercion が必要となるかもしれない関数適用 s t に
   ついて、適用されうる coercion を列挙する。

   * t の型が s の引数の型になるように t に coercion を適用する
   * s が t に適用できる関数になるように coercion を適用する
   * 適用必要がない ↔ identity を coercion として適用する

5. 型制約条件を列挙し、制約問題を解く。

   型制約条件は次の二種類

   * 関数適用 t1 t2 が行われていて、
     t1 : T1 かつ t2 : T2 （T1, T2 はメタ変数を含みうる）のとき
     T1 は T2 を引数にとる関数型でなければならない。i.e.
     T1 = Π x : T2, T3 x

   * definition foo : T := t
     のように宣言されている場合、
     t : T でなければならない。

   すべての関数適用と（あれば）全体の型から
   制約条件を列挙する。

   式 t1, t2, ... であって、
   メタ変数 ?M1, ?M2, ... に代入することで
   全ての制約条件をみたすものを見つける
   (unification problem)

   典型的な問題 (first-order) は簡単に解ける。
   制約条件
   f t_1 ... t_m = g s_1 ... s_m
   を考える。

   * f = g のときは、より小さいいくつかの制約条件
     t_1 = s_1, ..., t_m = s_m
     を解けばいい。

   * f ≠ g のときは解なし

   最終的に ?M = t の形になれば、そのメタ変数については解けたことになる。

   しかし higher-order unification problem は大変

   例） ?M a b = f (g a) b b の解は？
        * ?M = λ x y, f (g x) y y
        * ?M = λ x y, f (g x) y b
        * ?M = λ x y, f (g a) b y
        ...

   このような推論の問題は容易に発生しうる。
   -/
   check @sigma.mk
   check @nat.rec
   check @eq.subst
   /-
   上の関数は関数を implicit argument に持つ。

   このような問題を Lean は backtracking search で解く。
   second-order でも undecidable であることが知られているらしい。
   Lean の algorithm は
   x not complete (解がある場合でも失敗しうる）
   x potentailly nonterminating
   o performs quite well in ordinary situations

   さらに困ったことに、
   制約問題を解くために "計算" が必要になる場合がある。
   e.g. f M1? M2? = (λ x, f x x) M3?
        （β簡約を行わないと解けない）
   必要な計算の量はいくらでも大きくなりうる。
   ので、全ての簡約を試すのは現実的でない。
   ので、Lean は higher-order な制約を解くために
   簡約計算を行うことを避ける。
   これをさせない（Lean に簡約させる）ために、
   reducible attribute が使えるらしいが、
   これは Section 8.4 で説明する。

   Lean は制約条件を簡単なものから解いていくらしい。
   （確かにその方が効率が良さそう）

6. global backtracking search

   overload された notation や coercion についても選択の余地があるので、
   これらについても backtracking search を行う。

   まず、最初の候補（どれが最初？）で 5. を試し、
   失敗したら、その結果を解析し、
   次に試す選択肢を決める。

etc.

  他にも制約問題を解くための "わざ" があるらしい。
  tactic とか（あまり説明はない）
  あと class iference とか（これは次の章）
  このあたりはあまり理解できていません。
  (The elaborator relies on ... の段落)

まとめ.

  backtracking search で何から試すか、
  どの順番で試すかはこの tutorial では明らかにされてない。
  多分、実装依存というかこれから仕様変わる可能性がある。
  また、明示的に書かれていないが、探索の中でひとつ解が見つかれば、
  他の解の探索はしないようである。
  よって、Lean に複数の解釈の可能性を与える場合は
  型注釈をつける方が賢明

-/

end chapter8
