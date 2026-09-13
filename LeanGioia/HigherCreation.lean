import LeanGioia.SingleCreationComplete

/-!
# LeanGioia.HigherCreation

Checkpoint 13: the selected-term amplitude for the `n ≥ 2, m = 0`
pure-creation sector.

Appendix C.1.a first treats a pure-creation string

`s†_{j₁} ... s†_{jₙ}`

with `n ≥ 2`. Acting on the W state produces an `(n+1)`-particle
configuration obtained by occupying the creator sites together with a
distant site `l`.

This file formalizes that selected-term amplitude. For a duplicate-free
list of creator sites `js` and a site `l` outside that list, the pure
creation string has amplitude exactly `wCoefficient N` on the basis
configuration occupying `js ∪ {l}`.

The remaining paper step — proving that no different range-`R` term can
contribute to that same distant witness — is left to the next checkpoint.
-/

namespace LeanGioia

/--
Basis configuration occupying every creator site in `js` together with the
extra witness site `l`.
-/
def higherCreationWitnessBits {N : ℕ}
    (js : List (Fin N)) (l : Fin N) : Bitstring N :=
  occupiedBits (insert l js.toFinset)

/-- The extra witness site is occupied. -/
@[simp]
theorem higherCreationWitnessBits_extra {N : ℕ}
    (js : List (Fin N)) (l : Fin N) :
    higherCreationWitnessBits js l l = true := by
  simp [higherCreationWitnessBits, occupiedBits]

/-- Every creator site is occupied in the witness configuration. -/
@[simp]
theorem higherCreationWitnessBits_creator {N : ℕ}
    {js : List (Fin N)} {j l : Fin N} (hj : j ∈ js) :
    higherCreationWitnessBits js l j = true := by
  simp [higherCreationWitnessBits, occupiedBits, hj]

/--
With no creator sites, the higher-creation witness is exactly the usual
single-excitation basis configuration at `l`.
-/
theorem higherCreationWitnessBits_nil {N : ℕ} (l : Fin N) :
    higherCreationWitnessBits ([] : List (Fin N)) l =
      singleExcitationBits l := by
  funext x
  by_cases hx : x = l
  · subst x
    simp [higherCreationWitnessBits, occupiedBits, singleExcitationBits]
  · simp [higherCreationWitnessBits, occupiedBits, singleExcitationBits, hx]

/--
Removing the head creator from a duplicate-free witness leaves exactly the
witness associated with the tail.
-/
theorem setBit_higherCreationWitness_head_false {N : ℕ}
    {j l : Fin N} {js : List (Fin N)}
    (hnotmem : j ∉ js) (hjl : j ≠ l) :
    setBit (higherCreationWitnessBits (j :: js) l) j false =
      higherCreationWitnessBits js l := by
  funext x
  by_cases hxj : x = j
  · subst x
    simp [setBit, higherCreationWitnessBits, occupiedBits, hnotmem, hjl]
  · simp [setBit, higherCreationWitnessBits, occupiedBits, hxj]

/--
Selected-term amplitude corresponding to Eq. (C1).

For duplicate-free creator sites and an extra site outside the creator
list, the pure-creation string contributes exactly the W normalization
coefficient to the configuration occupying all creators plus the extra
site.
-/
theorem creationString_wState_higherCreationWitness {N : ℕ}
    (js : List (Fin N)) (l : Fin N)
    (hnodup : js.Nodup) (hl : l ∉ js) :
    creationString js (wState N) (higherCreationWitnessBits js l) =
      wCoefficient N := by
  induction js with
  | nil =>
      simp [creationString, higherCreationWitnessBits_nil,
        wState_apply_singleExcitation]
  | cons j js ih =>
      have hcons := List.nodup_cons.mp hnodup
      have hjnotmem : j ∉ js := hcons.1
      have htailnodup : js.Nodup := hcons.2
      have hjl : j ≠ l := by
        intro h
        subst j
        exact hl (by simp)
      have hltail : l ∉ js := by
        intro hmem
        exact hl (by simp [hmem])
      simp only [creationString, composeOperator_apply]
      change
        (if higherCreationWitnessBits (j :: js) l j = true
          then
            creationString js (wState N)
              (setBit (higherCreationWitnessBits (j :: js) l) j false)
          else 0) =
        wCoefficient N
      simp [setBit_higherCreationWitness_head_false hjnotmem hjl,
        ih htailnodup hltail]

/--
For a nonempty creator list and an extra site outside it, the witness lies
outside the one-particle W sector.
-/
theorem wState_higherCreationWitness_zero {N : ℕ}
    {j : Fin N} {js : List (Fin N)} {l : Fin N}
    (hnodup : (j :: js).Nodup) (hl : l ∉ (j :: js)) :
    wState N (higherCreationWitnessBits (j :: js) l) = 0 := by
  classical
  rw [wState_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro q hq
  apply basisState_apply_ne
  intro heq
  have hExtra := congrFun heq l
  have hCreator := congrFun heq j
  have hjl : j ≠ l := by
    intro h
    subst j
    exact hl (by simp)
  by_cases hql : q = l
  · subst q
    have hleft :
        higherCreationWitnessBits (j :: js) l j = true := by
      simp
    rw [hleft] at hCreator
    have hjl' : j = l := by
      simpa [singleExcitationBits] using hCreator
    exact hjl hjl'
  · have hleft :
        higherCreationWitnessBits (j :: js) l l = true := by
      simp
    rw [hleft] at hExtra
    have hlq : l = q := by
      simpa [singleExcitationBits] using hExtra
    exact hql hlq.symm

/--
The selected pure-creation term is nonzero on its higher-particle witness
for positive system size.
-/
theorem creationString_higherCreationWitness_nonzero {N : ℕ}
    (hN : 0 < N) (js : List (Fin N)) (l : Fin N)
    (hnodup : js.Nodup) (hl : l ∉ js) :
    creationString js (wState N) (higherCreationWitnessBits js l) ≠ 0 := by
  rw [creationString_wState_higherCreationWitness js l hnodup hl]
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by
    positivity
  simp [wCoefficient, hsqrt]

end LeanGioia
