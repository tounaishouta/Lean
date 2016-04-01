import standard

open nat

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n : nat}, A → vector A n → vector A (succ n)

open vector (nil cons)
infix `^` := vector
infixr ` :: ` := cons

definition uncons {A : Type} : Π {n : nat}, A^succ n → A × A^n :=
  have uncons' : Π {m : nat}, A^m → Π {n : nat}, m = succ n → A × A^n,
    from nat.rec (take va n H, nat.no_confusion H)
        (take m ih, vector.rec (take n H, nat.no_confusion H)
          (take n a va ih n' H, (a, eq.rec va (eq_of_succ_eq_succ H)))),
  take n va, uncons' va rfl

open prod (pr1 pr2)

definition head {A : Type} {n : ℕ} (va : A^succ n) : A :=
  pr1 (uncons va)

definition tail {A : Type} {n : ℕ} (va : A^succ n) : A^n :=
  pr2 (uncons va)

definition map {A B : Type} (f : A → B) {n : nat} : A^n → B^n :=
  vector.rec nil (take n a va map_va, f a :: map_va)

definition zipWith {A B C : Type} (f : A → B → C)
  : Π {k : nat}, A^k → B^k → C^k :=
  have aux : Π m : nat, A^m → Π n : nat, B^n → m = n → C^m,
    from take m, vector.rec
      (take n, vector.rec
        (assume H : 0 = 0, nil)
        (take n' b vb' ihb,
          assume H : 0 = succ n', nat.no_confusion H))
      (take m' a va' iha,
        take n, vector.rec
          (assume H : succ m' = 0, nat.no_confusion H)
          (take n' b vb' ihb,
            assume H : succ m' = succ n',
            have H' : m' = n', from eq_of_succ_eq_succ H,
            f a b :: iha n' vb' H')),
  take k va vb, aux k va k vb rfl

definition zipWith3 {A B C D : Type} (f : A → B → C → D)
  : Π {l : nat}, A^l → B^l → C^l → D^l :=
  have aux : Π m : nat, A^m → Π n : nat, B^n → m = n →
               Π k : nat, C^k → n = k → D^m,
       from take m, vector.rec
         (take n, vector.rec
           (assume Hmn : 0 = 0,
             take k, vector.rec
               (assume Hnk : 0 = 0,
                 nil)
               (take k' c vc' ihc,
                 assume Hnk : 0 = succ k',
                 nat.no_confusion Hnk))
           (take n' b vb' ihb,
             assume Hmn : 0 = succ n',
             nat.no_confusion Hmn))
         (take m' a va' iha,
           take n, vector.rec
             (assume Hmn : succ m' = 0,
               nat.no_confusion Hmn)
             (take n' b vb' ihb,
               assume Hmn : succ m' = succ n',
               take k, vector.rec
                 (assume Hnk : succ n' = 0,
                   nat.no_confusion Hnk)
                 (take k' c vc' ihc,
                   assume Hnk : succ n' = succ k',
                   have Hmn' : m' = n', from eq_of_succ_eq_succ Hmn,
                   have Hnk' : n' = k', from eq_of_succ_eq_succ Hnk,
                   f a b c :: @iha n' vb' Hmn' k' vc' Hnk'))),
  take l va vb vc, aux l va l vb rfl l vc rfl
