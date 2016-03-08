import standard

/-

Chapter 8. Building Theories and Proofs

実際的な Lean の機能について議論します。

Section 8.1 More on Coercions

前回、議論した coercion についてより詳しい説明をします。
まずは前回の復習
-/

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

open list

print list
print set --> : Type → Type := λ (X : Type), X → Prop

definition elem {A : Type} : A → list A → Prop
| elem _ nil       := false
| elem a (x :: xs) := a = x ∨ elem a xs

definition set_of_list [coercion] : Π A : Type, list A → set A
| set_of_list A xs := λ y : A, elem y xs

definition contains {A : Type} : list A → A → Prop
| contains xs y := elem y xs

set_option pp.coercions true

check λ (A : Type) (xs : set A) (y : A), xs y

/-

2. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), Type
   i.e. パラメータを持つ型 C から Type へ

例 C := Semigroup
-/

structure Semigroup :=
  (carrier : Type)
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

check Semigroup.carrier --> : Semigroup → Type
attribute Semigroup.carrier [coercion]

notation a `*` b := Semigroup.mul _ a b

-- 数学で代数構造などを持った対象 (S, *) と underlying set S を同じ記号で表す感覚
example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  calc (a * b) * c = a * (b * c) : Semigroup.mul_assoc

/-

3. Pi (x_1 : A_1) ... (x_n : A_n) (y: C x_1 ... x_n), (Pi x : A, B x)
   i.e. パラメータを持つ型 C から関数型へ
        A, B は x1, ..., x_n, y に依存してよい。

例 C := Semigroup.morphism, A := S1, B x := S2
-/

structure morphism (S1 S2 : Semigroup) :=
  (mor : S1 → S2 /- = carrier S → carrier S' -/)
  (resp_mul : ∀ a b : S1, mor (a * b) = mor a * mor b)

check @morphism.mor --> Π (S1 S2 : Semigroup), morphism S1 S2 → S1 → S2
attribute morphism.mor [coercion]

-- ”写像”が他の構造を持っているが関数として扱える。
example (S1 S2 : Semigroup) (f : morphism S1 S2) (a b : S1) :
  f (a * b) = f a * f b :=
  calc f (a * b) = f a * f b : morphism.resp_mul

/-
pp.coercions オプションにより print されるメッセージに
coercion を明示的に表示させることができる。
-/

set_option pp.coercions true

print morphism --> Semigroup.carrier が挿入されて表示される。

set_option pp.coercions false

print morphism

