import LeanGioia.SingleCreationOperator

/-!
# LeanGioia.SingleCreationComplete

Checkpoint 12: close the `n = 1, m = 0` pure-creation case end-to-end.

Checkpoint 11 proved that, for any selected site `j`, if there exist two
additional pairwise-distinct sites `l` and `p`, then the W-eigenstate
condition for the explicit single-creation operator forces `c j = 0`.

This file discharges that remaining site-existence hypothesis under the
minimal chain-size condition `3 ≤ N`.
-/

namespace LeanGioia

/--
For `N ≥ 3`, every site in `Fin N` has two additional pairwise-distinct
sites.
-/
theorem exists_two_other_sites {N : ℕ} (hN : 3 ≤ N) (j : Fin N) :
    ∃ l p : Fin N, j ≠ l ∧ j ≠ p ∧ l ≠ p := by
  classical
  have hcard : ({j} : Finset (Fin N)).card < N := by
    simp
    omega
  obtain ⟨l, hlj⟩ := exists_site_outside_of_card_lt ({j} : Finset (Fin N)) hcard
  have hjl : j ≠ l := by
    simpa using hlj
  have hcard2 : ({j, l} : Finset (Fin N)).card < N := by
    have hcard_pair : ({j, l} : Finset (Fin N)).card = 2 := by
      simp [hjl]
    rw [hcard_pair]
    omega
  obtain ⟨p, hp⟩ :=
    exists_site_outside_of_card_lt ({j, l} : Finset (Fin N)) hcard2
  have hjp : j ≠ p := by
    intro h
    subst p
    simp at hp
  have hlp : l ≠ p := by
    intro h
    subst p
    simp at hp
  exact ⟨l, p, hjl, hjp, hlp⟩

/--
For `N ≥ 3`, every coefficient of an explicit single-creation operator
having the W state as an eigenstate must vanish.
-/
theorem all_single_creation_coefficients_zero_of_eigenstate {N : ℕ}
    (hN : 3 ≤ N) (c : Fin N → ℂ) (eig : ℂ)
    (hEig : IsEigenstate (singleCreationOperator c) (wState N) eig) :
    ∀ j : Fin N, c j = 0 := by
  intro j
  obtain ⟨l, p, hjl, hjp, hlp⟩ := exists_two_other_sites hN j
  exact single_creation_coefficient_zero_of_eigenstate
    (by omega) c eig hEig hjl hjp hlp

/--
Function-level form of the complete single-creation obstruction.
-/
theorem single_creation_coefficients_zero_of_eigenstate {N : ℕ}
    (hN : 3 ≤ N) (c : Fin N → ℂ) (eig : ℂ)
    (hEig : IsEigenstate (singleCreationOperator c) (wState N) eig) :
    c = 0 := by
  funext j
  exact all_single_creation_coefficients_zero_of_eigenstate hN c eig hEig j

/--
Paper-facing end-to-end theorem for the `n = 1, m = 0` sector:

if `N ≥ 3` and the pure single-creation operator `G_c` has `|W⟩` as an
eigenstate, then all single-creation coefficients vanish.
-/
theorem single_creation_forbidden_of_eigenstate {N : ℕ}
    (hN : 3 ≤ N) (c : Fin N → ℂ) (eig : ℂ)
    (hEig : IsEigenstate (singleCreationOperator c) (wState N) eig) :
    SingleCreationForbidden c := by
  exact all_single_creation_coefficients_zero_of_eigenstate hN c eig hEig

end LeanGioia
