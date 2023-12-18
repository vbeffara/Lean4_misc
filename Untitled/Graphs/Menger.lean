import Mathlib
import Untitled.Graphs.Contraction
import Untitled.Graphs.Map
import Untitled.Graphs.Walk

set_option autoImplicit false

open Classical Function Finset

-- import combinatorics.SimpleGraph.connectivity data.Finset data.setoid.basic
-- import graph_theory.contraction graph_theory.pushforward graph_theory.basic graph_theory.walk
-- open Finset classical function SimpleGraph.Walk

variable {V V' : Type*} [Fintype V] [Fintype V']
variable {G G₁ G₂ : SimpleGraph V}
variable {a : V} {A B X Y Z : Finset V} -- {e : G.Dart}
-- variable {f : V → V'} {hf : G.Adapted f}

namespace SimpleGraph

namespace Menger

structure AB_Walk (G : SimpleGraph V) (A B : Finset V) :=
  (a b : V) (ha : a ∈ A) (hb : b ∈ B)
  (to_Walk : G.Walk a b)

-- variable {P : Finset (AB_Walk G A B)}

namespace AB_Walk

def Reverse (p : AB_Walk G A B) : AB_Walk G B A := ⟨p.b, p.a, p.hb, p.ha, p.to_Walk.reverse⟩

def Disjoint (p q : AB_Walk G A B) : Prop := List.Disjoint p.to_Walk.support q.to_Walk.support

def pwd (P : Finset (AB_Walk G A B)) : Prop := P.toSet.Pairwise Disjoint

def minimal (p : AB_Walk G A B) : Prop :=
  p.to_Walk.init' ∩ B = ∅ ∧ p.to_Walk.tail' ∩ A = ∅

-- noncomputable def lift (f : V → V') (hf : adapted f G) (A B : Finset V) :
--   AB_Walk (map f G) (A.image f) (B.image f) → AB_Walk G A B :=
-- begin
--   rintro ⟨p,ha,hb⟩,
--   choose a h₂ h₃ using mem_image.mp ha,
--   choose b h₅ h₆ using mem_image.mp hb,
--   let γ := Walk.pull_Walk_aux f hf p a b h₃ h₆,
--   rw ←γ.2.1 at h₂, rw ←γ.2.2.1 at h₅, exact ⟨γ,h₂,h₅⟩
-- end

-- def push (f : V → V') (A B : Finset V) :
--   AB_Walk G A B → AB_Walk (map f G) (A.image f) (B.image f) :=
-- begin
--   intro p, refine ⟨Walk.push_Walk f p.to_Walk, _, _⟩,
--   rw Walk.push_Walk_a, exact mem_image_of_mem f p.ha,
--   rw Walk.push_Walk_b, exact mem_image_of_mem f p.hb,
-- end

-- lemma push_lift : left_inverse (push f A B) (lift f hf A B) :=
-- by { rintro ⟨p,ha,hb⟩, simp [lift,push], exact Walk.pull_Walk_push }

-- lemma lift_inj : injective (lift f hf A B) :=
-- left_inverse.injective push_lift

-- noncomputable def trim_aux (p : AB_Walk G A B) :
--   {q : AB_Walk G A B // q.minimal ∧ q.to_Walk.range ⊆ p.to_Walk.range} :=
-- begin
--   rcases p with ⟨p₁, p₁a, p₁b⟩,
--   have h₁ : (p₁.range ∩ A).nonempty := ⟨p₁.a, by simp [p₁a]⟩,
--   rcases p₁.after A h₁ with ⟨p₂, p₂a, p₂b, p₂r, p₂i, -, p₂t⟩,
--   have h₂ : (p₂.range ∩ B).nonempty := by { refine ⟨p₂.b, _⟩, simp, rwa p₂b },
--   rcases p₂.until B h₂ with ⟨p₃, p₃a, p₃b, p₃r, p₃i, -, p₃t⟩,
--   refine ⟨⟨p₃, p₃a.symm ▸ p₂a, p₃b⟩, ⟨by simp [p₃i], _⟩, p₃r.trans p₂r⟩,
--   have : p₃.tail ∩ A ⊆ p₂.tail ∩ A := inter_subset_inter_right p₃t,
--   rw ←subset_empty, apply this.trans, rw p₂t, refl
-- end

-- noncomputable def trim (p : AB_Walk G A B) : AB_Walk G A B := p.trim_aux.val

-- lemma trim_minimal {p : AB_Walk G A B} : p.trim.minimal := p.trim_aux.prop.1

-- lemma trim_range {p : AB_Walk G A B} : p.trim.to_Walk.range ⊆ p.to_Walk.range := p.trim_aux.prop.2

-- noncomputable def massage_aux (h : G₂ ≤ G₁) (p : AB_Walk G₂ A X) :
--   {q : AB_Walk G₁ A X // q.minimal ∧ q.to_Walk.range ⊆ p.to_Walk.range} :=
-- begin
--   let p' := p.trim, rcases p'.to_Walk.transport (transportable_to_of_le h) with ⟨q,qa,qb,qr,qi,qt⟩,
--   refine ⟨⟨q, qa.symm ▸ p'.ha, qb.symm ▸ p'.hb⟩, _, _⟩,
--   { rw [minimal,qi,qt], exact trim_minimal },
--   { rw [qr], exact trim_range }
-- end

-- noncomputable def massage (h : G₂ ≤ G₁) (p : AB_Walk G₂ A X) : AB_Walk G₁ A X :=
-- (p.massage_aux h).val

end AB_Walk

open AB_Walk

-- namespace pwd

-- lemma le_A (dis : pwd P) : P.card ≤ A.card :=
-- begin
--   let φ : P → A := λ p, ⟨p.1.1.a, p.1.ha⟩,
--   have : injective φ := by { rintro p₁ p₂ h, simp at h, apply dis, use p₁.1.1.a, simp, simp [h] },
--   simp_rw [←Fintype.card_coe], convert Fintype.card_le_of_injective φ this,
-- end

-- lemma le_B (dis : pwd P) : P.card ≤ B.card :=
-- begin
--   let φ : P → B := λ p, ⟨p.val.b, p.val.hb⟩,
--   have : injective φ := by { rintro p₁ p₂ h, apply dis, use p₁.val.b, simp at h, simp, simp [h] },
--   simp_rw [←Fintype.card_coe], convert Fintype.card_le_of_injective φ this,
-- end

-- end pwd

def Separates (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ γ : AB_Walk G A B, ∃ x ∈ X, x ∈ γ.to_Walk.support

namespace Separates

lemma self : Separates G A B A := λ γ => ⟨γ.a, γ.ha, γ.to_Walk.start_mem_support⟩

lemma symm (h : Separates G A B X) : Separates G B A X := by
  intro p
  obtain ⟨x, h1, h2⟩ := h p.Reverse
  exact ⟨x, h1, by simpa [Reverse] using h2⟩

-- lemma comm : Separates G A B X ↔ Separates G B A X :=
-- ⟨Separates.symm,Separates.symm⟩

lemma inter_subset (h : Separates G A B X) : A ∩ B ⊆ X := by
  contrapose h
  obtain ⟨x, h1, h2⟩ := not_subset.mp h
  rw [mem_inter] at h1
  simp only [Separates, mem_coe, not_forall, not_exists, not_and]
  exact ⟨⟨x, x, h1.1, h1.2, Walk.nil⟩, by simp [h2]⟩

end Separates

def Separator (G : SimpleGraph V) (A B : Finset V) := {P : Finset V // Separates G A B P}

namespace Separator

def card (X : Separator G A B) : ℕ := X.val.card

instance : Nonempty (Separator G A B) := ⟨⟨A, Separates.self⟩⟩

def symm : Separator G A B → Separator G B A := λ ⟨X, sep⟩ => ⟨X, sep.symm⟩

@[simp] lemma card_symm {X : Separator G A B} : X.symm.card = X.card := by
  cases X
  simp [symm, card]

-- def comm : separator G A B ≃ separator G B A :=
-- { to_fun := symm,
--   inv_fun := symm,
--   left_inv := λ ⟨X,sep⟩, by simp only [symm],
--   right_inv := λ ⟨X,sep⟩, by simp only [symm] }

end Separator

def is_cut_set_size (G : SimpleGraph V) (A B : Finset V) (n : ℕ) : Prop :=
  ∃ X : Separator G A B, X.card = n

noncomputable def min_cut (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  @Nat.find (is_cut_set_size G A B) _ ⟨A.card, ⟨A, Separates.self⟩, rfl⟩

namespace min_cut

lemma symm : min_cut G A B = min_cut G B A := by
  simp_rw [min_cut]
  congr 1
  ext n
  constructor <;> exact λ ⟨X, h⟩ => ⟨X.symm, by simp [h]⟩

lemma spec : is_cut_set_size G A B (min_cut G A B) := Nat.find_spec _

noncomputable def set (G : SimpleGraph V) (A B : Finset V) :
    {X : Separator G A B // X.card = min_cut G A B} :=
  subtype_of_exists (spec)

-- lemma le {X : separator G A B} : min_cut G A B ≤ X.card :=
-- nat.find_le ⟨X, rfl⟩

-- lemma le' (sep : Separates G A B X) : min_cut G A B ≤ X.card :=
-- nat.find_le ⟨⟨X,sep⟩, rfl⟩

lemma inter_le_min_cut : (A ∩ B).card ≤ min_cut G A B := by
  rw [min_cut, Nat.le_find_iff]
  rintro n hn ⟨⟨X, h⟩, h'⟩
  simp only [Separator.card] at h'
  linarith [card_le_of_subset h.inter_subset]

end min_cut

def isMenger (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ A B : Finset V, ∃ P : Finset (AB_Walk G A B), pwd P ∧ P.card = min_cut G A B

lemma path_le_cut {P : Finset (AB_Walk G A B)} (dis : pwd P) (sep : Separates G A B X) :
    P.card ≤ X.card := sorry
-- begin
--   let φ : Π γ : P, γ.val.to_Walk.range ∩ X := λ γ, by { choose z hz using sep γ, exact ⟨z,hz⟩ },
--   let ψ : P → X := λ γ, ⟨_, mem_of_mem_inter_right (φ γ).prop⟩,
--   have h₁ : ∀ γ, (ψ γ).val ∈ γ.val.to_Walk.range := λ γ, let z := φ γ in (mem_inter.mp z.2).1,
--   have h₂ : injective ψ := λ γ γ' h, dis ⟨_, mem_inter_of_mem (h₁ γ) (by { rw h, exact (h₁ γ') })⟩,
--   simp_rw [←Fintype.card_coe], convert Fintype.card_le_of_injective ψ h₂
-- end

lemma upper_bound {P : Finset (AB_Walk G A B)} (dis : pwd P) : P.card ≤ min_cut G A B := by
  obtain ⟨⟨X, h₁⟩, h₂⟩ := min_cut.set G A B
  simpa [← h₂] using path_le_cut dis h₁

lemma bot_iff_no_edge : Fintype.card G.Dart = 0 ↔ G = ⊥ where
  mp h := by
    ext x y ; simp ; exact λ h' => isEmpty_iff.mp (Fintype.card_eq_zero_iff.mp h) ⟨⟨x, y⟩, h'⟩
  mpr h := by simpa only [h] using Fintype.card_eq_zero_iff.mpr <| isEmpty_iff.mpr Dart.is_adj

lemma bot_Separates_iff : Separates ⊥ A B X ↔ (A ∩ B) ⊆ X where
  mp := Separates.inter_subset
  mpr := λ h ⟨a, b, ha, hb, p⟩ => by cases p with
    | nil => exact ⟨a, h <| mem_inter.mpr ⟨ha, hb⟩, Walk.mem_support_nil_iff.mpr rfl⟩
    | cons h' _ => cases h'

lemma bot_min_cut : min_cut ⊥ A B = (A ∩ B).card := by
  refine le_antisymm ?_ min_cut.inter_le_min_cut
  rw [min_cut, Nat.find_le_iff]
  refine ⟨(A ∩ B).card, le_rfl, ?_⟩
  simpa only [is_cut_set_size] using ⟨⟨A ∩ B, bot_Separates_iff.mpr le_rfl⟩, rfl⟩

@[simp] lemma isMenger_bot : isMenger (⊥ : SimpleGraph V) := by
  rintro A B
  rw [bot_min_cut]
  let φ (z : (A ∩ B : Finset V)) : AB_Walk ⊥ A B :=
    let h := mem_inter.mp z.prop ; ⟨z, z, h.1, h.2, Walk.nil⟩
  have φ_inj : Injective φ := by intro u v h ; ext ; simp [φ] at h ; exact h.1
  refine ⟨image φ univ, ?_, by simp [card_image_of_injective, φ_inj]⟩
  rintro ⟨a, b, _, _, p⟩ hp ⟨a', b', _, _, q⟩ hq h
  simp at hp hq h
  rcases hp with ⟨rfl, -, h4⟩
  rcases hq with ⟨rfl, -, h8⟩
  subst_vars
  simp [AB_Walk.Disjoint]
  rintro rfl
  simp at h

-- lemma AB_lift_dis (P' : Finset (AB_Walk (map f G) (A.image f) (B.image f))) :
--   pwd P' → pwd (P'.image (AB_Walk.lift f hf A B)) :=
-- begin
--   rintro hP' ⟨γ₁,h₁⟩ ⟨γ₂,h₂⟩ h, simp at h ⊢, choose z h using h,
--   choose γ'₁ h'₁ h''₁ using mem_image.mp h₁,
--   choose γ'₂ h'₂ h''₂ using mem_image.mp h₂,
--   have h₃ := congr_arg (AB_Walk.push f A B) h''₁, rw AB_Walk.push_lift at h₃,
--   have h₄ := congr_arg (AB_Walk.push f A B) h''₂, rw AB_Walk.push_lift at h₄,
--   suffices : γ'₁ = γ'₂, { rw [←h''₁,←h''₂,this] },
--   have := @hP' ⟨_,h'₁⟩ ⟨_,h'₂⟩, simp at this, apply this,
--   simp [h₃,h₄,AB_Walk.push,Walk.push_range], use f z, rw mem_inter at h ⊢, split,
--   exact mem_image_of_mem f h.1, exact mem_image_of_mem f h.2
-- end

def minus (G : SimpleGraph V) (e : G.Dart) : SimpleGraph V :=
  G.deleteEdges {e.edge}

infix:60 " -ₑ " => minus

lemma minus_le {e : G.Dart} : G -ₑ e ≤ G := SimpleGraph.deleteEdges_le _ _

lemma minus_lt_edges {e : G.Dart} : Fintype.card (G -ₑ e).Dart < Fintype.card G.Dart := by
  let φ (f : (G -ₑ e).Dart) : G.Dart := ⟨f.1, f.is_adj.1⟩
  have φ_inj : Injective φ := by rintro e₁ e₂ h ; ext1 ; simpa [φ] using h
  suffices e ∉ Set.range φ from Fintype.card_lt_of_injective_of_not_mem φ φ_inj this
  rintro ⟨⟨⟨x, y⟩, he'⟩, he⟩
  simp [Dart.ext_iff, Prod.ext_iff] at he
  simp [minus, Dart.edge, he] at he'

-- lemma sep_AB_of_sep₂_AX ⦃e : G.Dart⦄ (ex_in_X : e.fst ∈ X) (ey_in_X : e.snd ∈ X) :
--   Separates G A B X → Separates (G-e) A X Z → Separates G A B Z :=
-- by {
--   rintro X_sep_AB Z_sep₂_AX γ,
--   rcases γ.to_Walk.until X (X_sep_AB γ) with ⟨δ,δ_a,δ_b,δ_range,δ_init,-⟩,
--   have : δ.transportable_to (G-e) := by {
--     revert δ_init, refine Walk.rec₀ _ _ δ,
--     { simp [Walk.transportable_to,Walk.edges] },
--     { rintro e' p h ih h₁ e'' h₂,
--       have h₃ : p.init ∩ X = ∅ :=
--       by { apply subset_empty.mp, rw [←h₁], apply inter_subset_inter_right,
--         rw [Walk.init_cons], apply subset_union_right },
--       simp at h₂, cases h₂,
--       { subst e'', simp at h₁, simp [minus,e'.is_Adj],
--         have : e'.fst ∉ X :=
--         by { rw [inter_distrib_right, union_eq_empty_iff] at h₁, intro h,
--           apply not_nonempty_empty, rw ←h₁.1,
--           exact ⟨e'.fst, by simp only [h, singleton_inter_of_mem, mem_singleton]⟩ },
--         intro h', apply this, rw [Dart.edge,sym2.mk_eq_mk_iff] at h',
--         cases h'; { rw h', assumption } },
--       { exact ih h₃ e'' h₂ }
--     }
--   },
--   rcases δ.transport this with ⟨ζ,ζ_a,ζ_b,ζ_range,-,-⟩,
--   rcases Z_sep₂_AX ⟨ζ, by { rw [ζ_a,δ_a], exact γ.ha }, by { rw [ζ_b], exact δ_b }⟩ with ⟨z,hz⟩,
--   rw ←ζ_range at δ_range, rw mem_inter at hz,
--   exact ⟨z, mem_inter.mpr ⟨mem_of_subset δ_range hz.1, hz.2⟩⟩,
-- }

-- lemma massage_eq {h : G₂ ≤ G₁} {P : Finset (AB_Walk G₂ A B)} {p₁ p₂ : P} :
--   pwd P → ((p₁.val.massage h).to_Walk.range ∩ (p₂.val.massage h).to_Walk.range).nonempty →
--   p₁ = p₂ :=
-- begin
--   rintro hP h, apply hP, rcases h with ⟨z,hz⟩, use z, simp at hz ⊢, split,
--   { apply (p₁.val.massage_aux h).prop.2, exact hz.1 },
--   { apply (p₂.val.massage_aux h).prop.2, exact hz.2 }
-- end

-- lemma massage_disjoint {h : G₂ ≤ G₁} {P : Finset (AB_Walk G₂ A B)} :
--   pwd P → pwd (image (AB_Walk.massage h) P) :=
-- begin
--   rintro h₁ ⟨p₁,hp₁⟩ ⟨p₂,hp₂⟩ h, apply subtype.ext, dsimp,
--   choose q₁ hq₁ hq₁' using mem_image.mp hp₁, choose q₂ hq₂ hq₂' using mem_image.mp hp₂,
--   rw [←hq₁',←hq₂'], apply congr_arg, let γ₁ : P := ⟨q₁,hq₁⟩, let γ₂ : P := ⟨q₂,hq₂⟩,
--   suffices : γ₁ = γ₂, { simp only [subtype.mk_eq_mk] at this, exact this }, apply massage_eq h₁,
--   rw [hq₁',hq₂'], exact h
-- end

-- lemma massage_card {h : G₂ ≤ G₁} {P : Finset (AB_Walk G₂ A B)} :
--   pwd P → (image (AB_Walk.massage h) P).card = P.card :=
-- begin
--   rintro hP, apply card_image_of_inj_on, rintro p₁ hp₁ p₂ hp₂ he,
--   let q₁ : P := ⟨p₁,hp₁⟩, let q₂ : P := ⟨p₂,hp₂⟩, suffices : q₁ = q₂, simp at this, exact this,
--   apply massage_eq hP, rw he, simp
-- end

-- lemma meet_sub_X (X_sep_AB : Separates G A B X) (p : AB_Walk G A X) (q : AB_Walk G B X)
--   (hp : p.minimal) (hq : q.minimal) : p.to_Walk.range ∩ q.to_Walk.range ⊆ X :=
-- begin
--   rcases p with ⟨p,pa,pb⟩, rcases q with ⟨q,qa,qb⟩, dsimp,
--   rintro x hx, rw mem_inter at hx, cases hx with hx₁ hx₂, by_contra,

--   rcases p.until {x} ⟨x, by simp [hx₁]⟩ with ⟨p', p'a, p'b, p'r, p'i, p'i2, p't⟩, simp at p'b,
--   have h₁ : p'.range ∩ X = ∅ :=
--   by { rw Walk.range_eq_init_union_last, rw inter_distrib_right, rw union_eq_empty_iff, split,
--     { exact subset_empty.mp ((inter_subset_inter_right p'i2).trans (subset_empty.mpr hp.1)) },
--     { rw p'b, exact singleton_inter_of_not_mem h } },

--   rcases q.until {x} ⟨x, by simp [hx₂]⟩ with ⟨q', q'a, q'b, q'r, q'i, q'i2, q't⟩, simp at q'b,
--   have h₁ : q'.range ∩ X = ∅ :=
--   by { rw Walk.range_eq_init_union_last, rw inter_distrib_right, rw union_eq_empty_iff, split,
--     { exact subset_empty.mp ((inter_subset_inter_right q'i2).trans (subset_empty.mpr hq.1)) },
--     { rw q'b, exact singleton_inter_of_not_mem h } },

--   let γ : AB_Walk G A B :=
--   ⟨Walk.append p' q'.reverse (by simp [p'b,q'b]), by simp [p'a,pa], by simp [q'a,qa]⟩,
--   choose z hz using X_sep_AB γ, rw [range_append,reverse_range,inter_distrib_right] at hz,
--   rw mem_union at hz, cases hz; { have := ne_empty_of_mem hz, contradiction }
-- end

-- noncomputable def endpoint (P : Finset (AB_Walk G A B))
--   (P_dis : pwd P) (P_eq : P.card = B.card) : P ≃ B :=
-- begin
--   let φ : P → B := λ p, let q := p.val in ⟨q.b,q.hb⟩,
--   apply equiv.of_bijective φ, rw Fintype.bijective_iff_injective_and_card, split,
--   { rintro p₁ p₂ h, apply P_dis, use p₁.val.b, simp at h ⊢, simp [h]  },
--   { simp, exact P_eq },
-- end

noncomputable def sep_cleanup {e : G.Dart} (ex_in_X : e.fst ∈ X) (ey_in_X : e.snd ∈ X)
  (X_eq_min : X.card = min_cut G A B) (X_sep_AB : Separates G A B X)
  (ih : ∃ (P : Finset (AB_Walk (G -ₑ e) A X)), pwd P ∧ P.card = min_cut (G -ₑ e) A X) :
  {P : Finset (AB_Walk G A X) // pwd P ∧ P.card = X.card ∧ ∀ p : P, p.val.minimal} := sorry
--   choose P h₁ h₂ using ih, use image (AB_Walk.massage minus_le) P, refine ⟨_,_,_⟩,
--   { exact massage_disjoint h₁ },
--   { apply (massage_card h₁).trans, apply le_antisymm h₁.le_B,
--     rcases min_cut.set (G-e) A X with ⟨⟨Z,Z_sep₂_AB⟩,Z_eq_min⟩,
--     rw [X_eq_min,h₂,←Z_eq_min], apply min_cut.le',
--     exact sep_AB_of_sep₂_AX ex_in_X ey_in_X X_sep_AB Z_sep₂_AB },
--   { intro p, choose p' hp'₁ hp'₂ using mem_image.mp p.prop,
--     have := (p'.massage_aux minus_le).prop.1, simp [AB_Walk.massage] at hp'₂, rw hp'₂ at this,
--     simp, exact this }

noncomputable def stitch (X_sep_AB : Separates G A B X)
  (P : Finset (AB_Walk G A X)) (P_dis: pwd P) (P_eq_X: P.card = X.card)
  (Q : Finset (AB_Walk G B X)) (Q_dis: pwd Q) (Q_eq_X: Q.card = X.card)
  (hP : ∀ p : P, p.val.minimal) (hQ : ∀ q : Q, q.val.minimal) :
  {R : Finset (AB_Walk G A B) // pwd R ∧ R.card = X.card} := sorry
-- begin
--   let φ : X ≃ P := (endpoint P P_dis P_eq_X).symm,
--   let ψ : X ≃ Q := (endpoint Q Q_dis Q_eq_X).symm,

--   have φxb : ∀ x : X, (φ x).val.b = x.val :=
--   by { intro x, set γ := φ x,
--     have : x = φ.symm γ := by simp only [equiv.symm_symm, equiv.apply_symm_apply],
--     rw this, refl },

--   have ψxb : ∀ x : X, (ψ x).val.b = x.val :=
--   by { intro x, set γ := ψ x,
--     have : x = ψ.symm γ := by simp only [equiv.symm_symm, equiv.apply_symm_apply],
--     rw this, refl },

--   let Ψ : X → AB_Walk G A B :=
--   by { intro x, set γ := φ x with hγ, set δ := ψ x with hδ,
--     have γbx : γ.val.b = x := φxb x, have δbx : δ.val.b = x := ψxb x,
--     set ζ := δ.val.to_Walk.reverse, refine ⟨Walk.append γ.val.to_Walk ζ _, _, _⟩,
--     { rw [γbx,←δbx,reverse_a] },
--     { rw [append_a], exact γ.val.ha },
--     { rw [append_b,reverse_b], exact δ.val.ha } },

--   set R := image Ψ univ,

--   have Ψ_inj : injective Ψ :=
--   by {
--     have : ∀ x : X, (Ψ x).to_Walk.range ∩ X = {x} :=
--     by { intro,
--       simp only [range_append, reverse_range],
--       simp_rw range_eq_init_union_last, simp_rw inter_distrib_right,
--       simp only [union_assoc],
--       rw [(hP (φ x)).1, (hQ (ψ x)).1, φxb, ψxb],
--       simp only [subtype.val_eq_coe,singleton_inter_of_mem,coe_mem,empty_union,union_idempotent] },
--     rintro x y h, ext, apply singleton_inj.mp, rw [← this x, ← this y, h] },

--   have l₁ : ∀ x y z, z ∈ (φ x).val.to_Walk.range ∩ (ψ y).val.to_Walk.range → x = y :=
--   by {
--     intros x y z hz,
--     have z_in_X : z ∈ X := meet_sub_X X_sep_AB (φ x) (ψ y) (hP (φ x)) (hQ (ψ y)) hz,
--     rw mem_inter at hz,
--     have z_is_x : z = x := by {
--       apply mem_singleton.mp, convert ← mem_inter.mpr ⟨hz.1,z_in_X⟩,
--       rw [range_eq_init_union_last, inter_distrib_right, φxb, (hP (φ x)).1],
--       simp only [subtype.val_eq_coe, singleton_inter_of_mem, coe_mem, empty_union], },
--     have z_is_y : z = y := by {
--       apply mem_singleton.mp, convert ← mem_inter.mpr ⟨hz.2,z_in_X⟩,
--       rw [range_eq_init_union_last, inter_distrib_right, ψxb, (hQ (ψ y)).1],
--       simp only [subtype.val_eq_coe, singleton_inter_of_mem, coe_mem, empty_union] },
--     ext, exact z_is_x.symm.trans z_is_y },

--   have R_dis : pwd R :=
--   by {
--     rintro ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩ h_dis,
--     choose x hx using mem_image.mp hγ₁, replace hx := hx.2, subst hx,
--     choose y hy using mem_image.mp hγ₂, replace hy := hy.2, subst hy,
--     suffices : x = y, subst this,
--     simp only [inter_distrib_left, inter_distrib_right, subtype.val_eq_coe, range_append,
--       reverse_range, union_assoc] at h_dis,
--     choose z hz using h_dis, simp only [mem_union] at hz,
--     cases hz, { apply φ.left_inv.injective, apply P_dis, use z, exact hz },
--     cases hz, { exact l₁ x y z hz },
--     cases hz, { rw inter_comm at hz, exact (l₁ y x z hz).symm },
--     { apply ψ.left_inv.injective, apply Q_dis, use z, exact hz }
--   },

--   refine ⟨R, R_dis, _⟩, rw card_image_of_injective _ Ψ_inj, convert Fintype.card_coe X
-- end

-- lemma sep_of_sep_in_merge : Separates (G/e) (image (merge_edge e) A) (image (merge_edge e) B) Y →
--   Separates G A B (Y ∪ {e.snd}) :=
-- begin
--   rintro Y_sep γ,
--   choose z hz using Y_sep (γ.push (merge_edge e) A B),
--   rw [mem_inter,AB_Walk.push,Walk.push_range,mem_image] at hz,
--   choose x hx₁ hx₂ using hz.1,
--   by_cases x = e.snd; simp [merge_edge,h] at hx₂,
--   { use x, simp, split, exact hx₁, right, exact h },
--   { use x, simp, split, exact hx₁, left, rw hx₂, exact hz.2 }
-- end

lemma step_1 {e} (h_contract : isMenger (G /ₑ e))
    (too_small : ∀ P : Finset (AB_Walk G A B), pwd P → P.card < min_cut G A B) :
    ∃ X : Finset V, e.fst ∈ X ∧ e.snd ∈ X ∧ Separates G A B X ∧ X.card = min_cut G A B := by
  let A₁ := image (merge_edge e) A
  let B₁ := image (merge_edge e) B
--   obtain ⟨Y, Y_eq_min₁⟩ := min_cut.set (G/e) A₁ B₁, let X := Y.to_Finset ∪ {e.snd},

--   have Y_lt_min : Y.card < min_cut G A B :=
--   by {
--     choose P₁ P₁_dis P₁_eq_min₁ using h_contract A₁ B₁,
--     rw [Y_eq_min₁, ←P₁_eq_min₁, ←card_image_of_injective P₁ AB_Walk.lift_inj],
--     apply too_small, { apply AB_lift_dis, exact P₁_dis }, { exact merge_edge_adapted }
--   },

--   have X_sep_AB : Separates G A B X := sep_of_sep_in_merge Y.sep,

--   refine ⟨X, _, _, X_sep_AB, _⟩,

--   { rw [mem_union], left, by_contradiction,
--     suffices : Separates G A B Y.to_Finset, by { exact not_lt_of_le (min_cut.le' this) Y_lt_min },
--     intro p, choose z hz using Y.sep (p.push (merge_edge e) A B), use z,
--     rw mem_inter at hz ⊢, rcases hz with ⟨hz₁,hz₂⟩, refine ⟨_,hz₂⟩,
--     rw [AB_Walk.push,Walk.push_range,mem_image] at hz₁, choose x hx₁ hx₂ using hz₁,
--     by_cases x = e.snd; simp [merge_edge,h] at hx₂,
--     { rw [←hx₂] at hz₂, contradiction },
--     { rwa [←hx₂] } },
--   { rw [mem_union,mem_singleton], right, refl },
--   { refine le_antisymm _ (min_cut.le' X_sep_AB),
--     exact (card_union_le _ _).trans (nat.succ_le_of_lt Y_lt_min) }
  sorry

lemma induction_step (e : G.Dart) : isMenger (G /ₑ e) → isMenger (G -ₑ e) → isMenger G := by
  intro h_contract h_minus A B
  apply not_imp_self.mp
  intro too_small
  push_neg at too_small
  replace too_small : ∀ P : Finset (AB_Walk G A B), pwd P → P.card < min_cut G A B
  · exact λ P h => lt_of_le_of_ne (upper_bound h) (too_small P h)
  obtain ⟨X, ex_in_X, ey_in_X, X_sep_AB, X_eq_min⟩ := step_1 h_contract too_small
  obtain ⟨P, hP⟩ := sep_cleanup ex_in_X ey_in_X X_eq_min X_sep_AB (h_minus A X)
  have X_eq_min' : X.card = min_cut G B A := X_eq_min.trans min_cut.symm
  obtain ⟨Q, hQ⟩ := sep_cleanup ex_in_X ey_in_X X_eq_min' X_sep_AB.symm (h_minus B X)
  rw [← X_eq_min]
  apply Subtype.exists_of_subtype
  exact stitch X_sep_AB P hP.1 hP.2.1 Q hQ.1 hQ.2.1 hP.2.2 hQ.2.2

theorem bla {α : Type*} (f : α → ℕ) {motive : α → Prop}
    (h1 : ∀ a, (∀ b, f b < f a → motive b) → motive a) {a} : motive a :=
  Nat.strongInductionOn (motive := fun x ↦ ∀ {a}, f a = x → motive a) (f a)
    (fun _ ih {a} h ↦ h1 a fun b hb ↦ ih (f b) (h ▸ hb) rfl) (Eq.refl (f a))

theorem graph_induction {motive : SimpleGraph V → Prop}
    (h1 : ∀ G, (∀ G', Fintype.card (Dart G') < Fintype.card (Dart G) → motive G') → motive G) :
    motive G :=
  bla (f := λ G => Fintype.card (Dart G)) h1

theorem Menger : isMenger G := by
  induction' h : Fintype.card G.Dart using Nat.strongInductionOn with n ih generalizing G
  subst h
  by_cases h' : Fintype.card G.Dart = 0
  · simp [bot_iff_no_edge.mp h']
  · have h2 : ¬ IsEmpty G.Dart := by simpa [← Fintype.card_eq_zero_iff]
    obtain ⟨e⟩ := not_isEmpty_iff.mp h2
    exact induction_step e (ih _ contract_edge.fewer_edges rfl) (ih _ minus_lt_edges rfl)

end Menger

end SimpleGraph
