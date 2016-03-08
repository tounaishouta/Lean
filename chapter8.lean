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

end chapter8
