module
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensionality in small weights

This file records basic `FiniteDimensional` results for modular forms on finite-index subgroups of
`SL(2, ℤ)`, using Mathlib's `NormTrace` API.

## Main statements
* `finiteDimensional_modularForm_neg_weight`
* `finiteDimensional_modularForm_weight_zero`
-/

namespace SpherePacking.ModularForms

open scoped MatrixGroups
open UpperHalfPlane ModularForm

noncomputable section

private lemma isArithmetic_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    (Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic :=
  (Subgroup.isArithmetic_iff_finiteIndex (Γ := Γ)).2 inferInstance

/-- Modular forms of negative weight form a finite-dimensional vector space. -/
public lemma finiteDimensional_modularForm_neg_weight (Γ : Subgroup SL(2, ℤ))
    (hΓ : Subgroup.index Γ ≠ 0)
    (k : ℤ) (hk : k < 0) : FiniteDimensional ℂ (ModularForm Γ k) := by
  haveI : Γ.FiniteIndex := ⟨hΓ⟩
  haveI : (Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic := isArithmetic_of_finiteIndex (Γ := Γ)
  have hz : ∀ f : ModularForm Γ k, f = 0 :=
    ModularForm.isZero_of_neg_weight (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (k := k) hk
  haveI : Subsingleton (ModularForm Γ k) := ⟨fun f g => by simp [hz f, hz g]⟩
  exact (Module.finite_def).2 Module.Finite.fg_top

/-- Modular forms of weight `0` are finite-dimensional (in fact, equivalent to `ℂ`). -/
public lemma finiteDimensional_modularForm_weight_zero (Γ : Subgroup SL(2, ℤ))
    (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ (0 : ℤ)) := by
  haveI : Γ.FiniteIndex := ⟨hΓ⟩
  haveI : (Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic := isArithmetic_of_finiteIndex (Γ := Γ)
  let e : ModularForm Γ (0 : ℤ) ≃ₗ[ℂ] ℂ :=
  { toFun := fun f => f I
    invFun := fun c => ModularForm.const (Γ := (Γ : Subgroup (GL (Fin 2) ℝ))) c
    left_inv := by
      intro f
      obtain ⟨c, hc⟩ :=
        ModularForm.eq_const_of_weight_zero (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) f
      ext z; simp [hc]
    right_inv := by intro c; rfl
    map_add' := by simp
    map_smul' := by simp }
  exact LinearEquiv.finiteDimensional e.symm

end

end SpherePacking.ModularForms
