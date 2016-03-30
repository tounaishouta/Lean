import standard

namespace chapter11

--
-- 前回の復習
--
namespace review
/-

Lean でも "begin .. end" の間や "by" の後には Coq のような
tactic-style の証明が書けますよー

-/
end review

--
-- 11.4 Structuring Tactic Proof
--
namespace section4
/-

Lean では term-style proof と tactic-style proof を自由に行き来できるよ、という話

e.g.

* term-style proof の中で

  * "begin <tactic-style proof> end"
    "begin" と "end" の間は tactic-style proof が書ける。

  * "by <single tactic>"
    "by" の後には tactic を 1 つだけ書ける。

  ("begin <tactic-style proof> end" は term として扱える、一応。)

  -/
  example (p : Prop) : p → p :=
    suppose p,
    begin intro, assumption end `p`
  /-

* tactic-style proof の中で

  * "apply <term-style proof>"

  * "exact <term-style proof>"

  * "show <type>, from <term-style proof>"

  term-style proof も term なので、
  term を書いていたところには term-style proof を書ける。

  -/
    example (p q : Prop) : p ∧ q → q ∧ p :=
      begin
        intro H,
        apply suppose q, suppose p, and.intro `q` `p`,
          exact and.right H,
        show p, from and.left H
      end
  /-

"begin .. end" は nest できる。
内側の "begin .. end" は "{ .. }" で代用できる。
内側のブロックでは、Lean は最初の subgoal だけを見る。
"end" あるいは "}" の時点でそれが証明できていないと error を起こす。

"{ ... }" を上手く使うと tacitc-style proof の構造を分かりやすくできる。
subgoal 数に応じた indent より個人的には好み。

-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    -- subgoal の確認の仕方
    -- * end にカーソルを合わせる
    -- * C-c ! l
    -- * C-c C-g
    apply iff.intro,
    { apply and.rec,
      intro Hp,
      apply or.rec,
      { intro Hq,
        exact or.inl (and.intro Hp Hq) },
      { intro Hr,
        exact or.inr (and.intro Hp Hr) }},
    { apply or.rec,
      { apply and.rec,
        intros Hp Hq,
        exact and.intro Hp (or.inl Hq) },
      { apply and.rec,
        intros Hp Hr,
        exact and.intro Hp (or.inr Hr) }}
  end
/-

We have adopted the convention that whenever a tactic increases the number of goals
to be solved, the tactics that solve each subsequent goal are enclosed in braces.
(証明木の木構造に応じた block 構造)

term style proof と対応

-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (and.rec
      (assume Hp,
        or.rec
          (assume Hq,
            or.inl (and.intro Hp Hq))
          (assume Hr,
            or.inr (and.intro Hp Hr))))
    (or.rec
      (and.rec
        (assume Hp Hq,
          and.intro Hp (or.inl Hq)))
      (and.rec
        (assume Hp Hr,
          and.intro Hp (or.inr Hr))))
/-

tactic-style proof の中でも、term-style proof のときと同じような
"have .., from ..." 構文か使える。
"from" の後は term-style proof が必要だが、
"begin .. end" あるいは "by ..." を使えば tacitc-style proof を書ける。
その場合は "from" は省略できる。
i.e.
  * have <identifier> : <Type>, by <single tactic>,
  * have <identifier> : <Type>, begin <tactic-style proof> end,

あと tutorial に多分書いてなかったけど "show" も使える。
"from" に関するルールは多分 "have" と同じ。
(exact の代わりに使えて型を明示するので読みやすい？)

-/
example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro H,
    have Hp : p,
      begin
        apply and.left,
        exact H
      end,
    have Hq : q, by apply and.right ; assumption,
    show q ∧ p, from and.intro Hq Hp
  end
/-

11.4 節は証明の書き方の話でした。
このあたりは好みが別れそうですね。
個人的には tactic-style である程度証明をバラして
細部は term-style で埋めるのが楽かと。
tactic-style での indent は "{ .. }" による構造に合わせるのが
term-style との整合性がとれて良いかと。

-/
end section4

--
-- 11.5 Cases and Pattern Matching
--
namespace section5

/-

cases tactic の話

仮定 (context, ⊢ の左側) をバラすのに使える。
本質的には "apply <inductive type>.cases_on," と等価。
広い意味での場合分け

具体例の中で使い方を見てみよう。

check @or.cases_on

-/
-- cases を使わない場合
example (p q : Prop) : p ∨ q → q ∨ p :=
  begin
    intro H,
    apply or.cases_on H,
    { intro Hp,
      exact or.inr Hp },
    { intro Hq,
      exact or.inl Hq }
  end

example (p q : Prop) : p ∨ q → q ∨ p :=
  begin
    intro H,
    cases H with Hp Hq, -- or "with [Hp, Hq],"
    -- with 以降が無いと勝手に名前を付けられる。
    { right, -- same as "apply or.inr," in this case
      exact Hp },
    { left, -- same as "apply or.inl," in this case
      exact Hq }
  end

-- check @and.cases_on

example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro H,
    cases H with Hp Hq,
    split, -- same as "apply and.intro," in this case
    { exact Hq },
    { exact Hp }
  end

open nat

example (n : ℕ) (H : n ≠ 0) : succ (pred n) = n :=
  begin
    cases n with m,
    { exact absurd rfl H },
    { calc succ (pred (succ m)) = succ m : pred_succ }
  end
/-

tutorial には載ってなかったが、
rec_on に対応して induction がある。

check @nat.cases_on
check @nat.rec_on

-/
example (n m k : ℕ) : (n + m) + k = n + (m + k) :=
  begin
    induction k with k IH, -- 同じ名前を使っても怒られない。
    { show (n + m) + 0 = n + (m + 0), from rfl },
    { calc (n + m) + succ k -- can also use "calc" in tactic-style
           = succ ((n + m) + k) : add_succ ...
           = succ (n + (m + k)) : IH ... -- cases と違って IH が使える。
           = n + succ (m + k)   : add_succ ...
           = n + (m + succ k)   : add_succ }
  end
/-

次は pattern match について。

tactic-style でも "match ... end" 構文が使える。
(cases を手動でやる感じ)

-/
example (p q : Prop) : p ∨ q → q ∨ p :=
  begin
    intro H,
    match H with
    | or.inl Hp := or.inr Hp
    | or.inr Hq := or.inl Hq
    end
  end

example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro H,
    match H with
    | and.intro Hp Hq := and.intro Hq Hp
    end
  end

example (n : ℕ) (H : n ≠ 0) : succ (pred n) = n :=
  begin
    revert H,
    match n with -- can also use "match" in tactic-style.
    | zero   := by intro H ; exact absurd rfl H
    | succ m := by intro H ; exact rfl
    end
  end
/-

cases (と induction) と pattern matching についてはこんな感じ。

途中ででてきた (Coq user におなじみの？) tactic を紹介。

tutorial 末尾の Quick Reference - A.6 Tactics で見つけました。

* split
  subgoal が constructor を 1 つ持つ inductive type のときに使える。
  (e.g. and, iff, ...)
  その唯一の constructor を apply する。

* left, right
  subgoal が constructor を 2 つ持つ inductive type のときに使える。
  (e.g. or, ...)
  left はその最初の constructor を、
  right は 2 番目の constructor を apply する。

* calc
  term-style の等式証明などに用いた calc は実は tactic-style でも
  そのまま使えました。


11.5 節まとめ

pattern match 自体は term-style でも出ていたので目新しいことはない。
ただ可読性でいえば term-style の cases_on より cases tactic の方がマシかと。
だが "match ... end" の方が読みやすいと思う。
"match .. end" でも帰納法を上手く回せるとよいのだけど。

-/
end section5

end chapter11
