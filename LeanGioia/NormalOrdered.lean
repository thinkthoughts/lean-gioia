import LeanGioia.CorollaryOne

/-!
# LeanGioia.NormalOrdered

Checkpoint 19: mixed normal-ordered syntax and the vacuum bridge.
-/

namespace LeanGioia

def annihilateAtNO {N : ℕ} (k : Fin N) : Operator N where
  toFun := fun ψ b =>
    if b k = false then ψ (setBit b k true) else 0
  map_add' := by
    intro ψ φ
    funext b
    by_cases h : b k = false
    · simp [h]
    · simp [h]
  map_smul' := by
    intro c ψ
    funext b
    by_cases h : b k = false
    · simp [h]
    · simp [h]

def annihilationStringNO {N : ℕ} : List (Fin N) → Operator N
  | [] => identityOperator N
  | k :: ks => annihilationStringNO ks ∘ₗ annihilateAtNO k

structure NormalOrderedTerm (N : ℕ) where
  creators : List (Fin N)
  annihilators : List (Fin N)

def NormalOrderedTerm.operator {N : ℕ}
    (t : NormalOrderedTerm N) : Operator N :=
  creationString t.creators ∘ₗ annihilationStringNO t.annihilators

theorem annihilateAtNO_vacuum {N : ℕ} (k : Fin N) :
    annihilateAtNO k (vacuumKet N) = 0 := by
  funext b
  by_cases hbk : b k = false
  · have hne :
        setBit b k true ≠ vacuumBits N := by
      intro hEq
      have hk := congrFun hEq k
      simp [setBit, vacuumBits] at hk
    simp [annihilateAtNO, hbk, vacuumKet, basisState, hne]
  · simp [annihilateAtNO, hbk]

theorem annihilationStringNO_vacuum_of_nonempty {N : ℕ}
    (ks : List (Fin N)) (hks : ks ≠ []) :
    annihilationStringNO ks (vacuumKet N) = 0 := by
  cases ks with
  | nil =>
      exact False.elim (hks rfl)
  | cons k ks =>
      simp only [annihilationStringNO, LinearMap.coe_comp,
        Function.comp_apply]
      rw [annihilateAtNO_vacuum]
      simp

theorem creationString_zero {N : ℕ} (js : List (Fin N)) :
    creationString js (0 : State N) = 0 := by
  induction js with
  | nil =>
      simp [creationString, identityOperator]
  | cons j js ih =>
      simp [creationString, composeOperator_apply, ih]

theorem normalOrderedTerm_vacuum_of_annihilators_nonempty {N : ℕ}
    (t : NormalOrderedTerm N)
    (hann : t.annihilators ≠ []) :
    t.operator (vacuumKet N) = 0 := by
  rw [NormalOrderedTerm.operator]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [annihilationStringNO_vacuum_of_nonempty t.annihilators hann]
  exact creationString_zero t.creators

theorem normalOrderedTerm_vacuumAnnihilating_of_nonempty {N : ℕ}
    (t : NormalOrderedTerm N)
    (hann : t.annihilators ≠ []) :
    VacuumAnnihilating t.operator := by
  exact normalOrderedTerm_vacuum_of_annihilators_nonempty t hann

theorem normalOrderedFamily_remainingTermsVacuumZero
    {N : ℕ} {ι : Type}
    (term : ι → NormalOrderedTerm N)
    (hann : ∀ i : ι, (term i).annihilators ≠ []) :
    ∀ i : ι, VacuumAnnihilating (term i).operator := by
  intro i
  exact normalOrderedTerm_vacuumAnnihilating_of_nonempty
    (term i) (hann i)

noncomputable def normalOrderedCorollaryOperator
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N) :
    Operator N :=
  corollaryOneOperator Ω coeff (fun i => (term i).operator)

theorem vacuum_eigenstate_of_normalOrdered_nonempty_annihilators
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (hann : ∀ i : ι, (term i).annihilators ≠ []) :
    IsEigenstate
      (normalOrderedCorollaryOperator Ω coeff term)
      (vacuumKet N) Ω := by
  unfold normalOrderedCorollaryOperator
  exact vacuum_eigenstate_of_no_pure_creation_remainder
    Ω coeff
    (fun i => (term i).operator)
    (normalOrderedFamily_remainingTermsVacuumZero term hann)

end LeanGioia
