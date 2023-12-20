import Mathlib
import Untitled.Graphs.Contraction

set_option autoImplicit false

open Classical SimpleGraph

variable {V V' : Type*} {a b c d : V} {G : SimpleGraph V} {p : G.Walk a b} {f : V → V'}

namespace SimpleGraph

namespace Walk

noncomputable def range (p : G.Walk a b) : Finset V := p.support.toFinset

@[simp] lemma range_cons {h : G.Adj a b} {p : G.Walk b c} : (cons h p).range = {a} ∪ p.range := by
  simp [range] ; rfl

@[simp] lemma range_append {q : G.Walk b c} : (append p q).range = p.range ∪ q.range := by
  ext ; simp [range]

@[simp] lemma range_copy {h1 : a = c} {h2 : b = d} :
    (p.copy h1 h2).range = p.range := by
  simp [range]

@[simp] lemma range_reverse : p.reverse.range = p.range := by simp [range]

noncomputable def init' {a b} : G.Walk a b → Finset V
| nil => {}
| cons _ p => insert a p.init'

@[simp] lemma init'_copy {h1 : a = c} {h2 : b = d} : (p.copy h1 h2).init' = p.init' := by
  induction p generalizing c d with
  | nil => subst_vars ; rfl
  | cons h p ih => rw [Walk.copy_cons] ; simp [init', ih, h1]

noncomputable def tail' {a b} : G.Walk a b → Finset V
| nil => {}
| cons _ p => p.range

end Walk

end SimpleGraph

-- import tactic combinatorics.simple_graph.connectivity
-- import graph_theory.path graph_theory.pushforward graph_theory.contraction
-- open classical function

-- namespace simple_graph

-- variables {V V' : Type*} [decidable_eq V] [decidable_eq V'] {f : V → V'}
-- variables {G G' : simple_graph V} {x y z u v w a b c : V}

-- structure Walk (G : simple_graph V) := {a b : V} (p : G.walk a b)

-- namespace Walk

-- variables {e : G.dart} {p q : G.Walk} {hep : e.snd = p.a} {hpq : p.b = q.a}

-- def nil (a : V) : G.Walk := ⟨(walk.nil : G.walk a a)⟩

-- @[simp] lemma nil_a : (nil a : G.Walk).a = a := rfl
-- @[simp] lemma nil_b : (nil b : G.Walk).b = b := rfl

-- def cons (e : G.dart) (p : G.Walk) (h : e.snd = p.a) : G.Walk :=
-- by { let h' := e.is_adj, rw h at h', exact ⟨p.p.cons h'⟩ }

def step (e : G.Dart) : G.Walk e.fst e.snd := Walk.cons e.is_adj Walk.nil

-- def rec₀ {motive : G.Walk → Sort*} :
--   (Π u, motive (Walk.nil u)) →
--   (Π e p h, motive p → motive (cons e p h)) →
--   Π p, motive p :=
-- λ h_nil h_cons ⟨p⟩, walk.rec_on p h_nil $ λ u v w h p, h_cons ⟨⟨_,_⟩,h⟩ ⟨p⟩ rfl

-- @[simp] lemma rec_nil {motive h_nil h_cons} :
--   @rec₀ V _ G motive h_nil h_cons (nil a) = h_nil a := rfl

-- @[simp] lemma rec_cons {motive h_nil h_cons h} :
--   @rec₀ V _ G motive h_nil h_cons (cons e p h) =
--   h_cons e p h (rec₀ h_nil h_cons p) :=
-- begin
--   rcases e with ⟨⟨u,v⟩,e⟩, rcases p with ⟨a,b,p⟩, dsimp only at h, subst v, refl
-- end

-- @[simp] lemma cons_a : (cons e p hep).a = e.fst := rfl
-- @[simp] lemma cons_b : (cons e p hep).b = p.b := rfl

-- @[simp] lemma range_cons : (cons e p hep).range = {e.fst} ∪ p.range :=
-- by simpa only [range, cons, walk.support_cons, list.to_finset_cons]

-- @[simp] lemma range_step : (step e).range = {e.fst, e.snd} :=
-- by simpa only [range, step, cons, walk.support_cons, list.to_finset_cons]

-- @[simp] lemma range_nonempty : p.range.nonempty :=
-- begin
--   refine rec₀ _ _ p,
--   { intro u, use u, simp [range] },
--   { intros e p h q, use e.fst, simp }
-- end

-- def init : G.Walk → finset V :=
-- rec₀ (λ v, ∅) (λ e p h q, {e.fst} ∪ q)

-- @[simp] lemma init_cons : (cons e p hep).init = {e.fst} ∪ p.init := rec_cons

lemma range_eq_init_union_last : p.range = p.init' ∪ {b} := by
  induction p with
  | nil => simp [Walk.range, Walk.init']
  | cons h p ih => simp [Walk.init', ih] ; rfl

-- by { refine rec₀ _ _ p, { intro u, refl }, { rintro e p h q, simp [q] } }

-- def tail : G.Walk → finset V :=
-- rec₀ (λ v, ∅) (λ e p h q, p.range)

-- @[simp] lemma tail_cons : (cons e p hep).tail = p.range := rec_cons

-- lemma range_eq_start_union_tail : p.range = {p.a} ∪ p.tail :=
-- by { refine rec₀ _ _ p, { intro, refl }, { intros, simp [*] } }

-- def edges : G.Walk → finset G.dart :=
-- rec₀ (λ v, ∅) (λ e p h q, {e} ∪ q)

-- @[simp] lemma edges_cons : (cons e p hep).edges = {e} ∪ p.edges := rec_cons

-- lemma first_edge : e ∈ (cons e p hep).edges := by simp

-- @[simp] lemma range_a : (nil a : G.Walk).range = {a} := rfl

-- @[simp] lemma start_mem_range : p.a ∈ p.range :=
-- by { refine rec₀ _ _ p; simp }

-- @[simp] lemma end_mem_range : p.b ∈ p.range :=
-- by { refine rec₀ _ _ p, simp, rintro e p h q, simp, right, exact q }

-- lemma range_eq_support : p.range = p.p.support.to_finset :=
-- begin
--   refine rec₀ _ _ p,
--   { intro u, refl },
--   { intros e p h q, rw [range_cons,q], ext, simpa }
-- end

-- def append_aux (p q : G.Walk) (hpq : p.b = q.a) : {w : G.Walk // w.a = p.a ∧ w.b = q.b} :=
-- begin
--   rcases p with ⟨a,b,p⟩, rcases q with ⟨c,d,q⟩, simp only at hpq, subst c,
--   refine ⟨⟨p ++ q⟩, rfl, rfl⟩,
-- end

-- def append_aux' (p q : G.Walk) (hpq : p.b = q.a) : {w : G.Walk // w.a = p.a ∧ w.b = q.b} :=
-- begin
--   rcases p with ⟨a,b,p⟩, rcases q with ⟨c,d,q⟩, simp only at hpq, subst c,
--   refine ⟨⟨p ++ q⟩, rfl, rfl⟩,
-- end

-- def append (p q : G.Walk) (hpq : p.b = q.a) : G.Walk :=
-- (append_aux p q hpq).val

-- @[simp] lemma append_a : (append p q hpq).a = p.a :=
-- (append_aux p q hpq).prop.1

-- @[simp] lemma append_b : (append p q hpq).b = q.b :=
-- (append_aux p q hpq).prop.2

-- @[simp] lemma append_nil_left {haq : a = q.a} : append (nil a) q haq = q :=
-- by { subst haq, rcases q with ⟨a,b,q⟩, refl }

-- @[simp] lemma append_cons :
--   append (cons e p hep) q hpq = cons e (append p q hpq) (by simp [hep]) :=
-- begin
--   rcases e with ⟨⟨u,v⟩,e⟩, rcases p with ⟨a,b,p⟩, rcases q with ⟨c,d,q⟩,
--   simp at hep hpq, substs a b, refl
-- end

-- lemma mem_append : z ∈ (append p q hpq).p.support ↔ z ∈ p.p.support ∨ z ∈ q.p.support :=
-- begin
--   rcases p with ⟨a,b,p⟩, rcases q with ⟨d,c,q⟩, simp at hpq, subst d,
--   rw [append, append_aux], simp only [walk.mem_support_append_iff]
-- end

-- noncomputable def push_step (f : V → V') (e : G.Dart) : (G.map' f).Walk (f e.fst) (f e.snd) := by
--   by_cases h : f e.fst = f e.snd
--   · rw [h]
--   · refine @step V' (G.map' f) ⟨(f e.fst, f e.snd), ?_⟩
--     simpa [map', h] using ⟨e.fst, e.snd, e.is_adj, rfl, rfl⟩

noncomputable def push_Walk {a b} (f : V → V') : G.Walk a b → (G.map' f).Walk (f a) (f b)
| Walk.nil => Walk.nil
| Walk.cons e p => by
  rename_i c
  by_cases h : f a = f c
  · exact (push_Walk f p).copy h.symm rfl
  · exact Walk.cons ⟨h, _, _, e, rfl, rfl⟩ (push_Walk f p)

-- @[simp] lemma push_nil : push_Walk f (@Walk.nil _ _ G a) = Walk.nil (f a) := rfl

-- lemma push_cons (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) :
--   push_Walk f (p.cons e h) = Walk.append (push_step f e) (push_Walk f p) (by simp [h]) :=
-- by { rcases p with ⟨a,b,p⟩, rcases e with ⟨⟨u,v⟩,e⟩, simp at h, subst a, refl }

-- lemma push_cons_eq (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) (h' : f e.fst = f e.snd) :
--   push_Walk f (p.cons e h) = push_Walk f p :=
-- begin
--   have : push_step f e = Walk.nil (f e.fst) := by simp [push_step,push_step_aux,h'],
--   rw [push_cons], simp only [this], exact append_nil_left
-- end

-- lemma push_cons_ne (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) (h' : f e.fst ≠ f e.snd) :
--   push_Walk f (p.cons e h) = Walk.cons ⟨⟨_,_⟩,⟨h',e.fst,e.snd,e.is_adj,rfl,rfl⟩⟩ (push_Walk f p) (by simp [h]) :=
-- begin
--   have : push_step f e = Walk.step ⟨⟨_,_⟩,⟨h',e.fst,e.snd,e.is_adj,rfl,rfl⟩⟩ :=
--     by simp [push_step,push_step_aux,h'],
--   rw [push_cons], simp [this,step]
-- end

-- lemma push_append (f : V → V') (p q : G.Walk) (hpq : p.b = q.a) :
--   push_Walk f (Walk.append p q hpq) =
--   Walk.append (push_Walk f p) (push_Walk f q) (by simp [hpq]) :=
-- begin
--   revert p, refine rec₀ (by simp) _,
--   intros e p h ih hpq, by_cases h' : f e.fst = f e.snd,
--   { have h₁ := push_cons_eq f e p h h',
--     have h₂ := push_cons_eq f e (Walk.append p q hpq) (h.trans append_a.symm) h',
--       simp only [h₁, h₂, ih, append_cons] },
--   { have h₁ := push_cons_ne f e p h h',
--     have h₂ := push_cons_ne f e (Walk.append p q hpq) (h.trans append_a.symm) h',
--       simpa only [h₁, h₂, ih, append_cons] }
-- end

-- lemma push_eq_nil (f : V → V') (w : V') (p : G.Walk) (hp : ∀ z : V, z ∈ p.p.support → f z = w) :
--   push_Walk f p = Walk.nil w :=
-- begin
--   revert p, refine rec₀ _ _,
--   { intros, specialize hp u (by simp [Walk.nil]), simp [hp] },
--   { intros e p h ih hp,
--     have h₁ : f e.fst = w := by { apply hp, left, refl },
--     have h₂ : f e.snd = w := by { apply hp, right, rw h, exact p.p.start_mem_support },
--     rw push_cons_eq f e p h (h₁.trans h₂.symm),
--     apply ih, intros z hz, apply hp, right, exact hz }
-- end

-- @[simp] lemma push_step_range : (push_step f e).range = {f e.fst, f e.snd} :=
-- by { by_cases f e.fst = f e.snd; simp [push_step, push_step_aux, h] }

@[simp] lemma push_range : (push_Walk f p).range = p.range.image f := by
  induction p with
  | nil => simp [Walk.range, push_Walk]
  | cons h p ih =>
    rename_i u v w
    by_cases h' : f u = f v <;> simp [push_Walk, h', ih, Finset.image_union]
    exact ⟨v, by simp [Walk.range], rfl⟩

-- variables {hf : adapted f G} {p' : (map f G).Walk} {hx : f x = p'.a} {hy : f y = p'.b}

noncomputable def pull_Walk_aux (f : V → V') (hf : G.Adapted f) (x y : V)
  (p' : (G.map' f).Walk (f x) (f y)) : {w : G.Walk x y // push_Walk f w = p'} := sorry
-- begin
--   revert p' x y, refine rec₀ _ _,
--   { rintros u x y hx hy, simp at hx hy, subst hy, choose p h₃ using hf hx,
--     refine ⟨⟨p⟩,rfl,rfl,_⟩, apply push_eq_nil, exact h₃ },
--   { rintros ⟨⟨u,v⟩,⟨huv,ee⟩⟩ p h ih x y hx hy,
--     choose xx yy h₂ h₃ h₄ using ee, substs h₃ h₄, choose p₁ h₆ using hf hx,
--     obtain p₂ := ih yy y (h) hy,
--     let pp := Walk.append ⟨p₁⟩ (p₂.val.cons ⟨⟨_,_⟩,h₂⟩ p₂.2.1.symm) rfl,
--     refine ⟨pp, rfl, p₂.2.2.1, _⟩,
--     have h₇ := push_eq_nil f (f xx) ⟨p₁⟩ h₆,
--     simp [pp,push_append,h₇],
--     have h₈ := push_cons_ne f ⟨⟨_,_⟩,h₂⟩ p₂.val p₂.2.1.symm huv, refine h₈.trans _,
--     congr, exact p₂.2.2.2 }
-- end

-- noncomputable def pull_Walk (f : V → V') (hf : adapted f G) (p' : (map f G).Walk) (x y : V)
--   (hx : f x = p'.a) (hy : f y = p'.b) : G.Walk :=
-- (pull_Walk_aux f hf p' x y hx hy).val

-- lemma pull_Walk_a : (pull_Walk f hf p' x y hx hy).a = x :=
-- (pull_Walk_aux f hf p' x y hx hy).prop.1

-- lemma pull_Walk_b : (pull_Walk f hf p' x y hx hy).b = y :=
-- (pull_Walk_aux f hf p' x y hx hy).prop.2.1

-- lemma pull_Walk_push : push_Walk f (pull_Walk f hf p' x y hx hy) = p' :=
-- (pull_Walk_aux f hf p' x y hx hy).prop.2.2

-- def transportable_to (G' : simple_graph V) (p : G.Walk) : Prop :=
--   ∀ e : G.dart, e ∈ p.edges → G'.adj e.fst e.snd

-- lemma transportable_to_of_le (G_le : G ≤ G') : p.transportable_to G' :=
-- begin
--   refine rec₀ _ _ p,
--   { rintro u e h, simp [edges] at h, contradiction },
--   { rintro e p h q e' h', simp at h', cases h', rw h', exact G_le e.is_adj, exact q e' h' }
-- end

-- def transport (p : G.Walk) (hp : transportable_to G' p) :
--   {q : G'.Walk // q.a = p.a ∧ q.b = p.b ∧ q.range = p.range ∧ q.init = p.init ∧ q.tail = p.tail} :=
-- begin
--   revert p, refine rec₀ _ _,
--   { rintro a hp, exact ⟨nil a, rfl, rfl, rfl, rfl, rfl⟩ },
--   { rintro e p h ih hp,
--     have : transportable_to G' p :=
--       by { rintro e he, apply hp, rw [edges_cons,finset.mem_union], right, exact he },
--     specialize ih this, rcases ih with ⟨q,hq⟩, rw ←hq.1 at h,
--     exact ⟨cons ⟨⟨_,_⟩,hp e first_edge⟩ q h, by simp [hq]⟩ }
-- end

noncomputable def entrance (p : G.Walk a b) (X : Finset V) (hX : (p.range ∩ X).Nonempty) :
    {x : V // x ∈ X ∧ x ∈ p.support } := by
  cases h : p.support.find? (· ∈ X) with
  | some a => exact ⟨a, by simpa using List.find?_some h, List.find?_mem h⟩
  | none =>
    choose z hz using hX
    simp only [Walk.range, Finset.mem_inter, List.mem_toFinset] at hz
    simpa [hz.2] using List.find?_eq_none.mp h z hz.1

noncomputable def exit (p : G.Walk a b) (X : Finset V) (hX : (p.range ∩ X).Nonempty) :
    {x : V // x ∈ X ∧ x ∈ p.support } := by
  let y := entrance p.reverse X (by simpa using hX)
  convert y using 3 ; simp

noncomputable def upto (p : G.Walk a b) (X : Finset V) (hX : (p.range ∩ X).Nonempty) :
    {q : G.Walk a (entrance p X hX) // q.support ⊆ p.support ∧ q.init' ∩ X = ∅ ∧ q.init' ⊆ p.init' ∧
      q.tail' ⊆ p.tail'} := by
  let x := entrance p X hX
  let q := p.takeUntil x.val x.prop.2
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact p.support_takeUntil_subset x.prop.2
  all_goals { sorry }
-- begin
--   revert p, refine rec₀ _ _,
--   { rintro u hu, choose z hz using hu, simp at hz, cases hz with hz₁ hz₂, subst z,
--     exact ⟨nil u, rfl, hz₂, by refl, rfl, by refl, by refl⟩ },
--   { rintro e p h₁ ih h₂, by_cases e.fst ∈ X,
--     { exact ⟨nil e.fst, rfl, h, by simp, rfl, by simp [init], by simp [tail]⟩ },
--     { simp at h₂, choose z hz using h₂, simp at hz, cases hz with hz₁ hz₂,
--       have : z ≠ e.fst := by { intro h, rw h at hz₂, contradiction },
--       simp [this] at hz₁,
--       have : z ∈ p.range ∩ X := finset.mem_inter.mpr ⟨hz₁,hz₂⟩,
--       specialize ih ⟨z,this⟩, rcases ih with ⟨q,hq₁,hq₂,hq₃,hq₄,hq₅,hq₆⟩,
--       rw ←hq₁ at h₁,
--       refine ⟨cons e q h₁, rfl, hq₂, _, _, _, by simp [hq₃]⟩,
--       { simp, apply finset.union_subset_union, refl, exact hq₃ },
--       { simp [finset.inter_distrib_right,hq₄,h] },
--       { simp, apply finset.union_subset_union, refl, exact hq₅ }
--     }
--   }
-- end

-- noncomputable def after (p : G.Walk) (X : finset V) (hX : (p.range ∩ X).nonempty) :
--   {q : G.Walk // q.a ∈ X ∧ q.b = p.b ∧
--     q.range ⊆ p.range ∧ q.init ⊆ p.init ∧ q.tail ⊆ p.tail ∧ q.tail ∩ X = ∅} :=
-- begin
--   revert p, refine rec₀ _ _,
--   { rintro u hu,
--     exact ⟨nil u, finset.singleton_inter_nonempty.mp hu, rfl, by refl, by refl, by refl, rfl⟩ },
--   { rintro e p h₁ ih h₂, by_cases (p.range ∩ X).nonempty,
--     { rcases ih h with ⟨q, hq₁, hq₂, hq₃, hq₄, hq₅, hq₆⟩,
--       refine ⟨q, hq₁, hq₂, _, _, _, hq₆⟩,
--       { simp, apply hq₃.trans, apply finset.subset_union_right },
--       { simp, apply hq₄.trans, apply finset.subset_union_right },
--       { simp, apply hq₅.trans, rw range_eq_start_union_tail, apply finset.subset_union_right }
--     },
--     { refine ⟨cons e p h₁, _, rfl, by refl, _⟩,
--       { simp at h₂ ⊢, rcases h₂ with ⟨z,hz⟩, simp at hz, cases hz with hz₁ hz₂,
--         cases hz₁, subst z, exact hz₂, exfalso, apply h, use z, simp, exact ⟨hz₁,hz₂⟩ },
--       { simp at h ⊢, exact h } } }
-- end

-- def reverse (p : G.Walk) : G.Walk := ⟨p.p.reverse⟩

-- @[simp] lemma reverse_a : (reverse p).a = p.b := by simp only [reverse]
-- @[simp] lemma reverse_b : (reverse p).b = p.a := by simp only [reverse]

-- @[simp] lemma reverse_range : (reverse p).range = p.range :=
-- by simp only [reverse, range, walk.support_reverse, list.to_finset_reverse]

-- end Walk

-- end simple_graph
