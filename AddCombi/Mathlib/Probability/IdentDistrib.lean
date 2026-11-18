module

public import Mathlib.Probability.IdentDistrib

public section

open MeasureTheory

namespace ProbabilityTheory
variable {Ω Ω' α : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω}
  {ν : Measure Ω'}

lemma _root_.MeasureTheory.MeasurePreserving.identDistrib {X : Ω' → α} {f : Ω → Ω'}
    [MeasurableSpace α] (hf : MeasurePreserving f μ ν) (hX : AEMeasurable X ν) :
    IdentDistrib X (X ∘ f) ν μ := by
  have A : AEMeasurable X (μ.map f) := by rwa [hf.map_eq]
  exact ⟨hX, A.comp_aemeasurable hf.aemeasurable,
    by rw [← AEMeasurable.map_map_of_aemeasurable A hf.aemeasurable, hf.map_eq]⟩

end ProbabilityTheory
