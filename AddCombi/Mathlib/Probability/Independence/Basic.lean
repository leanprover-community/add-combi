module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

public section

open MeasureTheory

namespace ProbabilityTheory
variable {Ω Ω' ι β γ : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {μ : Measure Ω} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- If `(f i)ᵢ` is an independent family under `μ` and `(g i)ᵢ` is an independent family under `ν`,
then `(f i × g i)ᵢ` is an independent family under `μ ⊗ ν`. -/
lemma iIndepFun.prodMap [Finite ι] {f : ι → Ω → β} {g : ι → Ω' → γ}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ i, AEMeasurable (g i) ν) (hfμ : iIndepFun f μ)
    (hgν : iIndepFun g ν) : iIndepFun (fun i ↦ Prod.map (f i) (g i)) (μ.prod ν) := by
  cases nonempty_fintype ι
  have hF : AEMeasurable (fun ω i ↦ f i ω) μ := .of_eval hf
  have hG : AEMeasurable (fun ω i ↦ g i ω) ν := .of_eval hg
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hf i).prodMap (hg i)]
  let e := MeasurableEquiv.arrowProdEquivProdArrow β γ ι
  calc
    (μ.prod ν).map (fun ω i ↦ Prod.map (f i) (g i) ω)
    _ = ((μ.prod ν).map (Prod.map (fun ω i ↦ f i ω) (fun ω i ↦ g i ω))).map e.symm :=
      (AEMeasurable.map_map_of_aemeasurable e.symm.measurable.aemeasurable (hF.prodMap hG)).symm
    _ = ((Measure.pi fun i ↦ μ.map (f i)).prod (Measure.pi fun i ↦ ν.map (g i))).map e.symm := by
      rw [← Measure.map_prod_map_of_aemeasurable _ _ hF hG,
        (iIndepFun_iff_map_fun_eq_pi_map hf).1 hfμ, (iIndepFun_iff_map_fun_eq_pi_map hg).1 hgν]
    _ = Measure.pi fun i ↦ (μ.map (f i)).prod (ν.map (g i)) :=
      ((measurePreserving_arrowProdEquivProdArrow β γ ι _ _).symm e).map_eq
    _ = Measure.pi fun i ↦ (μ.prod ν).map (Prod.map (f i) (g i)) := by
      simp_rw [Measure.map_prod_map_of_aemeasurable _ _ (hf _) (hg _)]

end ProbabilityTheory
