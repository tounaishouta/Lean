import standard

open nat

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n : nat}, A → vector A n → vector A (succ n)

open vector (nil cons)
infix `^` := vector
infixr ` :: ` := cons

definition uncons {A : Type} : Π {n : nat}, A^succ n → A × A^n :=
  have aux : Π m : nat, A^m → Π n : nat, m = succ n → A × A^n,
    from take m va, vector.cases_on va
      (take n, assume H : 0 = succ n,
        nat.no_confusion H)
      (take m' a va',
        take n, assume H : succ m' = succ n,
        (a, eq.rec va' (eq_of_succ_eq_succ H))),
  take n va, aux (succ n) va n rfl

open prod (pr1 pr2)

definition head {A : Type} {n : ℕ} (va : A^succ n) : A := pr1 (uncons va)

definition tail {A : Type} {n : ℕ} (va : A^succ n) : A^n := pr2 (uncons va)

definition map {A B : Type} (f : A → B) {n : nat} {va : A^n} : B^n :=
  vector.rec_on va nil (take n' a va' map_va', f a :: map_va')

definition zipWith {A B C : Type} (f : A → B → C)
  : Π {n : nat}, A^n → B^n → C^n :=
  have aux : Π n : nat, A^n → Π m : nat, B^m → n = m → C^n,
    from take n va, vector.rec_on va
      (take m vb, vector.cases_on vb
        (assume H : 0 = 0,
          nil)
        (take m' b vb',
          assume H : 0 = succ m',
          nat.no_confusion H))
      (take n' a va' IH,
        take m vb, vector.cases_on vb
          (assume H : succ n' = 0,
            nat.no_confusion H)
          (take m' b vb',
            assume H : succ n' = succ m',
            have H' : n' = m', from eq_of_succ_eq_succ H,
            f a b :: IH m' vb' H')),
  take n va vb, aux n va n vb rfl

-- use "head" and "tail"
definition zipWith' {A B C : Type} (f : A → B → C) {n : nat}
  : A^n → B^n → C^n :=
  nat.rec_on n
    proof take va vb, nil qed -- fail to elaborate without "proof" and "qed"
    proof take m IH va vb, f (head va) (head vb) :: IH (tail va) (tail vb) qed

definition zipWith3 {A B C D : Type} (f : A → B → C → D)
  : Π {n : nat}, A^n → B^n → C^n → D^n :=
  have aux : Π n : nat, A^n → Π m : nat, B^m → n = m → Π k : nat, C^k → m = k → D^n,
    from take n va, vector.rec_on va
      (take m vb, vector.cases_on vb
        (assume Hnm : 0 = 0,
          take k vc, vector.cases_on vc
            (assume Hmk : 0 = 0,
              nil)
            (take k' c vc',
              assume Hmk : 0 = succ k',
              nat.no_confusion Hmk))
        (take m' b vb',
          assume Hnm : 0 = succ m',
          nat.no_confusion Hnm))
      (take n' a va' IH,
        take m va, vector.cases_on va
          (assume Hnm : succ n' = 0,
            nat.no_confusion Hnm)
          (take m' b vb',
            assume Hnm : succ n' = succ m',
            have Hnm' : n' = m', from eq_of_succ_eq_succ Hnm,
            take k vc, vector.cases_on vc
              (assume Hmk : succ m' = 0,
                nat.no_confusion Hmk)
              (take k' c vc',
                assume Hmk : succ m' = succ k',
                have Hmk' : m' = k', from eq_of_succ_eq_succ Hmk,
                f a b c :: IH m' vb' Hnm' k' vc' Hmk'))),
  take n va vb vc, aux n va n vb rfl n vc rfl

-- use "zipWith" twice
definition zipWith3' {A B C D : Type} (f : A → B → C → D)
  {n : nat} (va : A^n) (vb : B^n) (vc : C^n) : D^n :=
  zipWith id (zipWith f va vb) vc
