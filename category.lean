import standard

structure Category :=
  (Ob : Type)
  (Hom : Ob → Ob → Type)
  (comp : Π {a b c : Ob}, Hom b c → Hom a b → Hom a c)
  (id : Π {a : Ob}, Hom a a)
  (comp_assoc : ∀ {a b c d : Ob} {h : Hom c d} {g : Hom b c} {f : Hom a b},
                comp (comp h g) f = comp h (comp g f))
  (comp_id : ∀ {a b : Ob} {f : Hom a b}, comp f id = f)
  (id_comp : ∀ {a b : Ob} {f : Hom a b}, comp id f = f)

namespace Category

attribute Ob [coercion]

notation g `∘` f := comp _ g f

example (C : Category) (a b c d : C) (h : Hom C c d) (g : Hom C b c) (f : Hom C a b)
  : (h ∘ g) ∘ f = h ∘ (g ∘ f)
  := Category.comp_assoc C

example (C : Category) (a b : C) (f : Hom C a b)
  : f ∘ id C = f
  := Category.comp_id C

example (C : Category) (a b : C) (f : Hom C a b)
  : id C ∘ f = f
  := Category.id_comp C

definition op [reducible] (C : Category)
  : Category
  := ⦃ Category
     , Ob := Ob C
     , Hom := λ a b : C, Hom C b a
     , comp := λ a b c g f, f ∘ g
     , id := λ a, id C
     , comp_assoc
       := take a b c d h g f, eq.symm (comp_assoc C)
     , comp_id
       := take a b f, id_comp C
     , id_comp
       := take a b f, comp_id C
     ⦄
  
definition Type_as_Category : Category :=
  ⦃ Category
  , Ob := Type
  , Hom := λ X Y : Type, X → Y
  , comp := λ (X Y Z : Type) (g : Y → Z) (f : X → Y) (x : X), g (f x)
  , id := λ (X : Type) (x : X), x
  , comp_assoc := take X Y Z W h g f, rfl
  , comp_id := take X Y f, rfl
  , id_comp := take X Y f, rfl
  ⦄

structure functor (C D : Category) :=
  (map_Ob : C → D)
  (map_Hom : Π {a b : C}, Hom C a b → Hom D (map_Ob a) (map_Ob b))
  (resp_comp : ∀ {a b c : C} {g : Hom C b c} {f : Hom C a b},
               map_Hom (comp C g f) = comp D (map_Hom g) (map_Hom f))
  (resp_id : ∀ {a : C}, map_Hom (@id C a) = @id D (map_Ob a))

attribute functor.map_Ob [coercion]
attribute functor.map_Hom [coercion]

structure nat_trans {C D : Category} (F G : functor C D) :=
  (map : Π a : C, Hom D (F a) (G a))
  (comm : ∀ {a b : C} {f : Hom C a b}, G f ∘ map a = map b ∘ F f)

attribute nat_trans.map [coercion]

definition functor_category (C D : Category) : Category :=
  ⦃ Category
  , Ob := functor C D
  , Hom := λ F G : functor C D, nat_trans F G
  , comp :=
    λ F G H : functor C D,
    λ eta : nat_trans G H,
    λ xi : nat_trans F G,
    ⦃ nat_trans F H 
    , map := λ a : C, eta a ∘ xi a
    , comm :=
      take a b : C,
      take f : Hom C a b,
      calc H f ∘ (eta a ∘ xi a)
           = (H f ∘ eta a) ∘ xi a : comp_assoc
      ...  = (eta b ∘ G f) ∘ xi a : nat_trans.comm eta
      ...  = eta b ∘ (G f ∘ xi a) : comp_assoc
      ...  = eta b ∘ (xi b ∘ F f) : nat_trans.comm xi
      ...  = (eta b ∘ xi b) ∘ F f : comp_assoc
    ⦄
  , id :=
    take F : functor C D,
    ⦃ nat_trans F F
    , map := λ a, id D
    , comm :=
      take a b : C,
      take f : Hom C a b,
      calc F f ∘ id D
           = F f        : comp_id
      ...  = id D ∘ F f : id_comp
    ⦄
  , comp_assoc := sorry
  , comp_id := sorry
  , id_comp := sorry
  ⦄

-- structure の等号を示す術を僕達はまだ知らない。
-- 関数の等号を外延性から示す術を僕達はまだ知らない。

definition presheaf (C : Category)
  : Category
  := functor_category (op C) Type_as_Category

end Category  
