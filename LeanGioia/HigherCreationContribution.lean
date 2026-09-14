import LeanGioia.HigherCreationUniqueness

/-!
# LeanGioia.HigherCreationContribution

Checkpoint 15: nonzero creation-string amplitude implies a witness-set
representation.

Checkpoint 14 formalized the finite-set uniqueness statement used in
Appendix C.1.a.  This checkpoint supplies the operator-amplitude bridge.

For a pure-creation string `creationString ks`, a nonzero amplitude on a
basis configuration means:

1. every creator site in `ks` is occupied in the output configuration;
2. after clearing those creator sites, the remaining input configuration
   has nonzero W amplitude;
3. therefore that cleared configuration is a single-excitation basis state.

Applied to the selected higher-particle witness for creator list `js` and
extra site `l`, this yields a site `q` satisfying

`insert q ks.toFinset = insert l js.toFinset`,

which is exactly `RepresentsHigherCreationWitness`.
-/

namespace LeanGioia

/-- Clear every site listed in `ks` from a computational-basis configuration. -/
def clearSites {N : ℕ} : List (Fin N) → Bitstring N → Bitstring N
  | [], b => b
  | k :: ks, b => clearSites ks (setBit b k false)

/-- Clearing sites not containing `x` leaves the bit at `x` unchanged. -/
theorem clearSites_apply_of_not_mem {N : ℕ}
    (ks : List (Fin N)) (b : Bitstring N) {x : Fin N}
    (hx : x ∉ ks) :
    clearSites ks b x = b x := by
  induction ks generalizing b with
  | nil =>
      rfl
  | cons k ks ih =>
      have hxk : x ≠ k := by
        intro h
        subst x
        exact hx (by simp)
      have hxtail : x ∉ ks := by
        intro h
        exact hx (by simp [h])
      simp only [clearSites]
      rw [ih (setBit b k false) hxtail]
      simp [setBit, hxk]

/--
If a bit remains occupied after clearing sites, then it was occupied in the
original configuration.
-/
theorem clearSites_true_implies_original_true {N : ℕ}
    (ks : List (Fin N)) (b : Bitstring N) (x : Fin N)
    (h : clearSites ks b x = true) :
    b x = true := by
  induction ks generalizing b with
  | nil =>
      simpa [clearSites] using h
  | cons k ks ih =>
      have h' : setBit b k false x = true := by
        exact ih (setBit b k false) h
      by_cases hxk : x = k
      · subst x
        simp [setBit] at h'
      · simpa [setBit, hxk] using h'

/--
A nonzero pure-creation-string amplitude implies that every creator site is
occupied in the output basis configuration.
-/
theorem creationString_nonzero_creator_occupied {N : ℕ}
    (ks : List (Fin N)) (b : Bitstring N)
    (h :
      creationString ks (wState N) b ≠ 0) :
    ∀ k ∈ ks, b k = true := by
  induction ks generalizing b with
  | nil =>
      simp
  | cons j js ih =>
      have hj : b j = true := by
        by_cases hb : b j = true
        · exact hb
        · have hz :
            creationString (j :: js) (wState N) b = 0 := by
            simp [creationString, composeOperator_apply, createAt, hb]
          exact False.elim (h hz)
      intro k hk
      rcases List.mem_cons.mp hk with rfl | htail
      · exact hj
      · have htailnz :
          creationString js (wState N) (setBit b j false) ≠ 0 := by
          intro hz
          apply h
          simp [creationString, composeOperator_apply, createAt, hj, hz]
        have hkclear :
            setBit b j false k = true :=
          ih (setBit b j false) htailnz k htail
        by_cases hkj : k = j
        · subst k
          simp [setBit] at hkclear
        · simpa [setBit, hkj] using hkclear

/--
A nonzero creation-string amplitude leaves a configuration with nonzero W
amplitude after all creator sites are cleared.
-/
theorem creationString_nonzero_wState_clearSites {N : ℕ}
    (ks : List (Fin N)) (b : Bitstring N)
    (h :
      creationString ks (wState N) b ≠ 0) :
    wState N (clearSites ks b) ≠ 0 := by
  induction ks generalizing b with
  | nil =>
      simpa [creationString, clearSites, identityOperator] using h
  | cons j js ih =>
      have hj : b j = true := by
        by_cases hb : b j = true
        · exact hb
        · have hz :
            creationString (j :: js) (wState N) b = 0 := by
            simp [creationString, composeOperator_apply, createAt, hb]
          exact False.elim (h hz)
      have htail :
          creationString js (wState N) (setBit b j false) ≠ 0 := by
        intro hz
        apply h
        simp [creationString, composeOperator_apply, createAt, hj, hz]
      simpa [clearSites] using
        ih (setBit b j false) htail

/--
Any computational-basis configuration on which the W state has nonzero
amplitude is one of the single-excitation basis configurations.
-/
theorem exists_singleExcitation_of_wState_ne_zero {N : ℕ}
    (b : Bitstring N) (h : wState N b ≠ 0) :
    ∃ q : Fin N, b = singleExcitationBits q := by
  classical
  by_contra hnone
  push Not at hnone
  apply h
  rw [wState_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro q hq
  apply basisState_apply_ne
  exact hnone q

/--
A nonzero pure-creation-string amplitude determines a single W-input site
after clearing the creator sites.
-/
theorem creationString_nonzero_exists_input_site {N : ℕ}
    (ks : List (Fin N)) (b : Bitstring N)
    (h :
      creationString ks (wState N) b ≠ 0) :
    ∃ q : Fin N, clearSites ks b = singleExcitationBits q := by
  exact exists_singleExcitation_of_wState_ne_zero
    (clearSites ks b)
    (creationString_nonzero_wState_clearSites ks b h)

/--
Checkpoint-15 bridge:

if a competing pure-creation string has nonzero amplitude on the selected
higher-particle witness, then its creator set, together with one W-input
site `q`, represents exactly that witness set.
-/
theorem creationString_nonzero_represents_higherCreationWitness {N : ℕ}
    (js ks : List (Fin N)) (l : Fin N)
    (h :
      creationString ks (wState N)
        (higherCreationWitnessBits js l) ≠ 0) :
    ∃ q : Fin N,
      RepresentsHigherCreationWitness js.toFinset l q ks.toFinset := by
  classical
  obtain ⟨q, hclear⟩ :=
    creationString_nonzero_exists_input_site
      ks (higherCreationWitnessBits js l) h
  refine ⟨q, ?_⟩
  unfold RepresentsHigherCreationWitness
  ext x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with hxq | hxks
    · subst x
      have hclearq :
          clearSites ks (higherCreationWitnessBits js l) q = true := by
        rw [hclear]
        simp [singleExcitationBits]
      have hwq :
          higherCreationWitnessBits js l q = true :=
        clearSites_true_implies_original_true
          ks (higherCreationWitnessBits js l) q hclearq
      simpa [higherCreationWitnessBits, occupiedBits] using hwq
    · have hxlist : x ∈ ks := by
        simpa using hxks
      have hwx :
          higherCreationWitnessBits js l x = true :=
        creationString_nonzero_creator_occupied
          ks (higherCreationWitnessBits js l) h x hxlist
      simpa [higherCreationWitnessBits, occupiedBits] using hwx
  · intro hx
    by_cases hxks : x ∈ ks.toFinset
    · exact Finset.mem_insert_of_mem hxks
    · have hxlist : x ∉ ks := by
        simpa using hxks
      have hwx :
          higherCreationWitnessBits js l x = true := by
        simpa [higherCreationWitnessBits, occupiedBits] using hx
      have hclearx :
          clearSites ks (higherCreationWitnessBits js l) x = true := by
        rw [clearSites_apply_of_not_mem ks
          (higherCreationWitnessBits js l) hxlist]
        exact hwx
      rw [hclear] at hclearx
      have hxq : x = q := by
        simpa [singleExcitationBits] using hclearx
      subst x
      simp

end LeanGioia
