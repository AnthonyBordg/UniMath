(** Anthony Bordg, August 2017 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Categories.

Local Open Scope cat.

Definition prebicategory_ob_mor_2mor : UU :=
  ∑ C : precategory_ob_mor, ∏ a b : ob C, ∏ f g : a --> b, UU.

Definition prebicategory_ob_mor_2mor_to_precategory_ob_mor (C : prebicategory_ob_mor_2mor) : precategory_ob_mor := pr1 C.

Coercion prebicategory_ob_mor_2mor_to_precategory_ob_mor : prebicategory_ob_mor_2mor >-> precategory_ob_mor.

Definition prebicategory_2morphisms {C : prebicategory_ob_mor_2mor} {a b : ob C} : ∏ f g : a --> b, UU := pr2 C a b.

Delimit Scope bicat with bicat.

Close Scope Cat.

Local Open Scope bicat.

Notation "a -1-> b" := (precategory_morphisms a b) (at level 75) : bicat.

Notation "f -2-> g" := (prebicategory_2morphisms f g) (at level 75) : bicat.

Definition prebicategory_id_comp_1 : UU :=
  ∑ C : prebicategory_ob_mor_2mor, (∏ c : ob C, c -1-> c) × (∏ a b c : ob C, a -1-> b -> b -1-> c -> a -1-> c).

Definition prebicategory_id_comp_1_to_prebicategory_ob_mor_2mor (C : prebicategory_id_comp_1) : prebicategory_ob_mor_2mor := pr1 C.

Coercion prebicategory_id_comp_1_to_prebicategory_ob_mor_2mor : prebicategory_id_comp_1 >-> prebicategory_ob_mor_2mor.

Definition identity_mor {C : prebicategory_id_comp_1} {c : ob C} : c -1-> c := pr1 (pr2 C) c.

Definition compose_mor {C : prebicategory_id_comp_1} {a b c : ob C} : a -1-> b -> b -1-> c -> a -1-> c := pr2 (pr2 C) a b c.

Notation "f · g" := (compose_mor f g) : bicat.

Definition identity_2mor (C : prebicategory_id_comp_1) : UU := ∏ a b : ob C, ∏ f : a -1-> b, f -2-> f.

Definition comp_2mor_vertical (C : prebicategory_id_comp_1) : UU :=
  ∏ a b : ob C, ∏ f g h : a -1-> b, f -2-> g -> g -2-> h -> f -2-> h.

Definition comp_2mor_horizontal (C : prebicategory_id_comp_1) : UU :=
  ∏ a b c : ob C, ∏ f f' : a -1-> b, ∏ g g' : b -1-> c, f -2-> f' -> g -2-> g' -> f · g -2-> f' · g' .

Definition prebicategory_id_comp_2 (C : prebicategory_id_comp_1) : UU :=
  (identity_2mor C) × (comp_2mor_vertical C) × (comp_2mor_horizontal C).

Definition prebicategory_id_comp : UU := ∑ C : prebicategory_id_comp_1, prebicategory_id_comp_2 C.

Definition prebicategory_id_comp_to_prebicategory_id_comp_1 (C : prebicategory_id_comp) : prebicategory_id_comp_1 := pr1 C.

Coercion prebicategory_id_comp_to_prebicategory_id_comp_1 : prebicategory_id_comp >-> prebicategory_id_comp_1 .

Definition compose_2mor_vertical {C : prebicategory_id_comp} {a b : ob C} {f g h : a -1-> b} :
  f -2-> g -> g -2-> h -> f -2-> h := pr1 (pr2 (pr2 C)) a b f g h.

Notation "α ·v· β" := (compose_2mor_vertical α β) (at level 75) : bicat.

Definition is_assoc_comp_2mor_vertical (C : prebicategory_id_comp) : UU :=
  ∏ a b : ob C, ∏ f g h i : a -1-> b, ∏ α : f -2-> g, ∏ β : g -2-> h, ∏ γ : h -2-> i, (α ·v· (β ·v· γ)) = ((α ·v· β) ·v· γ) .

Definition id_2mor {C : prebicategory_id_comp} {a b : ob C} : ∏ f : a -1-> b, f -2-> f := pr1 (pr2 C) a b.

Definition comp_2mor_vertical_ax (C : prebicategory_id_comp) : UU :=
  (∏ (a b : C) (f g : a -1-> b) (α : f -2-> g), (id_2mor f ·v· α) = α)
    × (∏ (a b : C) (f g : a -1-> b) (α : f -2-> g), (α ·v· id_2mor g) = α)
      × is_assoc_comp_2mor_vertical C.

Definition homprecategory_ob_mor {C : prebicategory_id_comp} (a b : C) : precategory_ob_mor :=
  precategory_ob_mor_pair (pr2 (pr1 (pr1 (pr1 C))) a b) (pr2 (pr1 (pr1 C)) a b) .




Definition compose_2mor_horizontal {C : prebicategory_data} {a b c : ob C} {f f' : a -1-> b}
           {g g' : b -1-> c} : f -2-> f' -> g -2-> g' -> (f · g) -2-> (f' · g') := pr2 (pr2 (pr2 (pr2 C))) a b c f f' g g'.

Notation "α ·h· β" := (compose_2mor_horizontal α β) (at level 75) : bicat.