import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

open Classical Function

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {e : G.Dart}

def Minus (G : SimpleGraph V) (e : G.Dart) : SimpleGraph V :=
  G.deleteEdges {e.edge}

infix:60 " -ₑ " => Minus

@[simp] lemma Minus_le : G -ₑ e ≤ G := deleteEdges_le _ _

lemma minus_lt_edges : Fintype.card (G -ₑ e).Dart < Fintype.card G.Dart := by
  let φ (f : (G -ₑ e).Dart) : G.Dart := ⟨f.1, f.is_adj.1⟩
  have φ_inj : Injective φ := by rintro e₁ e₂ h ; ext1 ; simpa [φ] using h
  suffices e ∉ Set.range φ from Fintype.card_lt_of_injective_of_not_mem φ φ_inj this
  rintro ⟨⟨⟨x, y⟩, he'⟩, he⟩
  simp [Dart.ext_iff, Prod.ext_iff] at he
  simp [Minus, Dart.edge, he] at he'

end SimpleGraph
