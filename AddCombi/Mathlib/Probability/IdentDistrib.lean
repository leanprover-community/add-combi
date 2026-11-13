module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

/-!
# Identically distributed random variables

Material in this file is copied from the PFR project.
-/

public section

open MeasureTheory

namespace ProbabilityTheory
variable {Ω Ω' α β : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'}

/-- If `F i` and `F' i` are identically distributed for all `i` and both families are independent,
then the vectors `(F i)ᵢ` and `(F' i)ᵢ` are identically distributed. -/
lemma IdentDistrib.pi {I : Type*} [Finite I] {F : I → Ω → β} {F' : I → Ω' → β}
    (hFF' : ∀ i, IdentDistrib (F i) (F' i) μ ν) (h : iIndepFun F μ) (h' : iIndepFun F' ν) :
    IdentDistrib (fun x i ↦ F i x) (fun x i ↦ F' i x) μ ν where
  aemeasurable_fst := .of_eval fun i ↦ (hFF' i).aemeasurable_fst
  aemeasurable_snd := .of_eval fun i ↦ (hFF' i).aemeasurable_snd
  map_eq := by
    cases nonempty_fintype I
    have := h.isProbabilityMeasure
    have := h'.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hFF' i).aemeasurable_fst).1 h,
      (iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hFF' i).aemeasurable_snd).1 h']
    congr with i : 1
    exact (hFF' i).map_eq

lemma _root_.MeasureTheory.MeasurePreserving.identDistrib {X : Ω' → α} {f : Ω → Ω'}
    [MeasurableSpace α] (hf : MeasurePreserving f μ ν) (hX : AEMeasurable X ν) :
    IdentDistrib X (X ∘ f) ν μ := by
  have A : AEMeasurable X (μ.map f) := by rwa [hf.map_eq]
  exact ⟨hX, A.comp_aemeasurable hf.aemeasurable,
    by rw [← AEMeasurable.map_map_of_aemeasurable A hf.aemeasurable, hf.map_eq]⟩

end ProbabilityTheory
