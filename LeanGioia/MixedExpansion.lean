import LeanGioia.NormalOrdered

/-!
# LeanGioia.MixedExpansion

Checkpoint 20: one finite mixed normal-ordered expansion and the
Table-I-Row-1 → Corollary-1 bridge.

A nonidentity normal-ordered basis term has either a creator or an
annihilator.  Table I Row 1 excludes precisely the nonidentity terms with
no annihilators:

`creators ≠ [] ∧ annihilators = []  →  coefficient = 0`.

Hence every term that can contribute nontrivially to the vacuum either has
zero coefficient or has a nonempty annihilator list.  Checkpoint 19 proves
that the latter terms annihilate the vacuum.

This closes the structural bridge used in the paper's Corollary 1
argument for a finite mixed normal-ordered expansion.
-/

namespace LeanGioia

/--
The mixed-expansion form of Table I Row 1:
every nonidentity pure-creation term has zero coefficient.
-/
def MixedRowOneCondition
    {N : ℕ} {ι : Type}
    (coeff : ι → ℂ) (term : ι → NormalOrderedTerm N) : Prop :=
  ∀ i : ι,
    (term i).annihilators = [] →
    (term i).creators ≠ [] →
    coeff i = 0

/--
The finite family contains only nonidentity normal-ordered terms.
The identity contribution is carried separately by `Ω`.
-/
def NonidentityNormalOrderedFamily
    {N : ℕ} {ι : Type}
    (term : ι → NormalOrderedTerm N) : Prop :=
  ∀ i : ι,
    (term i).creators ≠ [] ∨ (term i).annihilators ≠ []

/-- The nonidentity remainder of one finite mixed normal-ordered expansion. -/
noncomputable def mixedNormalOrderedRemainder
    {N : ℕ} {ι : Type} [Fintype ι]
    (coeff : ι → ℂ) (term : ι → NormalOrderedTerm N) :
    Operator N :=
  ∑ i : ι, coeff i • (term i).operator

/--
Full mixed expansion with the identity coefficient separated:

`G = Ω 1 + Σᵢ cᵢ Tᵢ`.
-/
noncomputable def mixedNormalOrderedOperator
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N) :
    Operator N :=
  Ω • identityOperator N + mixedNormalOrderedRemainder coeff term

/--
Table I Row 1 plus nonidentity syntax implies that every summand of the
mixed remainder contributes zero on the vacuum.

If the annihilator list is empty, the term is nonidentity only through a
nonempty creator list, so Row 1 sets its coefficient to zero.

If the annihilator list is nonempty, Checkpoint 19 shows the term itself
annihilates the vacuum.
-/
theorem mixedNormalOrdered_summand_vacuum_zero
    {N : ℕ} {ι : Type}
    (coeff : ι → ℂ) (term : ι → NormalOrderedTerm N)
    (hrow : MixedRowOneCondition coeff term)
    (hnonid : NonidentityNormalOrderedFamily term)
    (i : ι) :
    coeff i • (term i).operator (vacuumKet N) = 0 := by
  by_cases hann : (term i).annihilators = []
  · have hcre : (term i).creators ≠ [] := by
      rcases hnonid i with hcre | hann'
      · exact hcre
      · exact False.elim (hann' hann)
    have hc : coeff i = 0 := hrow i hann hcre
    rw [hc]
    simp
  · have hz :
        (term i).operator (vacuumKet N) = 0 :=
      normalOrderedTerm_vacuum_of_annihilators_nonempty
        (term i) hann
    rw [hz]
    simp

/--
The entire nonidentity mixed remainder annihilates the vacuum.
-/
theorem mixedNormalOrderedRemainder_vacuum_zero
    {N : ℕ} {ι : Type} [Fintype ι]
    (coeff : ι → ℂ) (term : ι → NormalOrderedTerm N)
    (hrow : MixedRowOneCondition coeff term)
    (hnonid : NonidentityNormalOrderedFamily term) :
    mixedNormalOrderedRemainder coeff term (vacuumKet N) = 0 := by
  classical
  rw [mixedNormalOrderedRemainder]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact mixedNormalOrdered_summand_vacuum_zero
    coeff term hrow hnonid i

/--
Checkpoint-20 Corollary-1 theorem for one finite mixed normal-ordered
expansion.

Once Table I Row 1 excludes all nonidentity pure-creation coefficients,
the vacuum is an eigenstate and its eigenvalue is exactly the identity
coefficient `Ω`.
-/
theorem vacuum_eigenstate_of_mixedRowOne
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (hrow : MixedRowOneCondition coeff term)
    (hnonid : NonidentityNormalOrderedFamily term) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω coeff term)
      (vacuumKet N) Ω := by
  apply (isEigenstate_iff_amplitudes
    (mixedNormalOrderedOperator Ω coeff term)
    (vacuumKet N) Ω).2
  intro b
  rw [mixedNormalOrderedOperator]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  have hz :=
    mixedNormalOrderedRemainder_vacuum_zero
      coeff term hrow hnonid
  have hzb :
      mixedNormalOrderedRemainder coeff term (vacuumKet N) b = 0 := by
    exact congrFun hz b
  rw [Pi.add_apply, hzb]
  simp [identityOperator]

/--
Paper-facing packaged statement:
the Row-1 coefficient condition on a finite mixed normal-ordered expansion
is sufficient for the vacuum-eigenstate conclusion.
-/
structure MixedCorollaryOneData
    {N : ℕ} {ι : Type}
    (coeff : ι → ℂ) (term : ι → NormalOrderedTerm N) : Prop where
  rowOne : MixedRowOneCondition coeff term
  nonidentity : NonidentityNormalOrderedFamily term

theorem corollary_one_for_finite_mixed_expansion
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (h : MixedCorollaryOneData coeff term) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω coeff term)
      (vacuumKet N) Ω := by
  exact vacuum_eigenstate_of_mixedRowOne
    Ω coeff term h.rowOne h.nonidentity

end LeanGioia
