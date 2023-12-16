import Mathlib

set_option autoImplicit false

open ENNReal MeasureTheory ProbabilityTheory

variable {α : Type*} {m1 m2 : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} {hm : m1 ≤ m2}

namespace Measure_theory

lemma Lp.integrable [IsFiniteMeasure μ] {p : ℝ≥0∞} [T : Fact (1 ≤ p)] (f : Lp ℝ p μ) :
    Integrable f μ :=
  (Lp.memℒp f).integrable T.out

lemma L2.integrable_mul : ∀ (f g : Lp ℝ 2 μ), Integrable (fun x => f x * g x) μ := by
  apply L2.integrable_inner

noncomputable def Lp_trim_to_Lp (p : ℝ≥0∞) (μ : Measure α) (hm : m1 ≤ m2) :
    Lp ℝ p (μ.trim hm) → Lp ℝ p μ :=
  λ f => lpTrimToLpMeas ℝ ℝ p μ hm f

namespace Lp_trim_to_Lp

lemma ae_eq {f : Lp ℝ p (μ.trim hm)} : Lp_trim_to_Lp p μ hm f =ᵐ[μ] f := by
  apply lpTrimToLpMeas_ae_eq

lemma snorm {f : Lp ℝ p (μ.trim hm)} : snorm (Lp_trim_to_Lp p μ hm f) p μ = snorm f p μ :=
  snorm_congr_ae ae_eq

lemma isometry [T : Fact (1 ≤ p)] : Isometry (Lp_trim_to_Lp p μ hm) := by
  rintro f g
  rw [Lp.edist_def, Lp.edist_def]
  rw [snorm_trim_ae hm ((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g))]
  exact snorm_congr_ae (ae_eq.sub ae_eq)

@[continuity] lemma continuous [Fact (1 ≤ p)] : Continuous (Lp_trim_to_Lp p μ hm) :=
  Lp_trim_to_Lp.isometry.continuous

end Lp_trim_to_Lp

@[continuity] lemma continuous_integral_trim : Continuous (λ f : Lp ℝ 1 (μ.trim hm) => integral μ f) := by
  simp_rw [← integral_congr_ae Lp_trim_to_Lp.ae_eq]
  exact continuous_integral.comp Lp_trim_to_Lp.isometry.continuous

@[continuity] lemma continuous_set_integral_trim {S : Set α} :
    Continuous (λ f : Lp ℝ 1 (μ.trim hm) => ∫ a in S, f a ∂μ) := by
  simp_rw [← integral_congr_ae Lp_trim_to_Lp.ae_eq.restrict]
  exact (continuous_set_integral S).comp Lp_trim_to_Lp.isometry.continuous

end Measure_theory

open Measure_theory

namespace probability_theory

theorem indep_fun.integral_mul_of_Lp [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {X Y : Lp ℝ p μ} (hXY : IndepFun X Y μ) :
    integral μ (fun x => X x * Y x) = integral μ X * integral μ Y :=
  hXY.integral_mul_of_integrable (Lp.integrable X) (Lp.integrable Y)

end probability_theory
