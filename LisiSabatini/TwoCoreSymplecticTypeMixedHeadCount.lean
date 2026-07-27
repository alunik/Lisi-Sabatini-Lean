import LisiSabatini.TwoCoreSymplecticTypeMixedCount

/-!
# Square fibers in maximal-class two-group heads

This file discharges the head-side finite input used by the mixed
central-product count.  The proof is entirely by the three explicit
normal forms.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- A fiber of multiplication by `m` on a finite residue group. -/
abbrev NsmulZModFiber (n m : ℕ) (t : ZMod n) :=
  {x : ZMod n // m • x = t}

/-- Every nonempty fiber of an additive homomorphism is a translate of
its kernel. -/
private noncomputable def nsmulZModFiberEquivKer
    (n m : ℕ) (t : ZMod n)
    (a : NsmulZModFiber n m t) :
    NsmulZModFiber n m t ≃
      (nsmulAddMonoidHom m : ZMod n →+ ZMod n).ker where
  toFun x := ⟨x.1 - a.1, by
    apply AddMonoidHom.mem_ker.mpr
    change m • (x.1 - a.1) = 0
    rw [nsmul_sub, x.2, a.2, sub_self]⟩
  invFun x := ⟨a.1 + x.1, by
    rw [nsmul_add, a.2]
    have hx :
        m • x.1 = 0 :=
      AddMonoidHom.mem_ker.mp x.2
    rw [hx, add_zero]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- A scalar fiber on `ZMod n` has at most `gcd n m` elements. -/
theorem natCard_nsmulZModFiber_le_gcd
    (n m : ℕ) (hn : 0 < n) (t : ZMod n) :
    Nat.card (NsmulZModFiber n m t) ≤ n.gcd m := by
  letI : NeZero n := ⟨hn.ne'⟩
  by_cases hnonempty : Nonempty (NsmulZModFiber n m t)
  · let a : NsmulZModFiber n m t := Classical.choice hnonempty
    calc
      Nat.card (NsmulZModFiber n m t) =
          Nat.card
            (nsmulAddMonoidHom m :
              ZMod n →+ ZMod n).ker :=
        Nat.card_congr (nsmulZModFiberEquivKer n m t a)
      _ = n.gcd m := by
        rw [IsAddCyclic.card_nsmulAddMonoidHom_ker]
        simp only [Nat.card_zmod]
      _ ≤ n.gcd m := le_rfl
  · haveI : IsEmpty (NsmulZModFiber n m t) :=
      not_nonempty_iff.mp hnonempty
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- Doubling on an even nonzero residue group has fibers of size at most
two. -/
theorem natCard_two_nsmulZModFiber_le_two
    (m : ℕ) (hm : 0 < m) (t : ZMod (2 * m)) :
    Nat.card (NsmulZModFiber (2 * m) 2 t) ≤ 2 := by
  calc
    Nat.card (NsmulZModFiber (2 * m) 2 t) ≤
        (2 * m).gcd 2 :=
      natCard_nsmulZModFiber_le_gcd
        (2 * m) 2 (by omega) t
    _ = 2 := by
      calc
        (2 * m).gcd 2 = (2 * m).gcd (2 * 1) := by rw [mul_one]
        _ = 2 * m.gcd 1 := Nat.gcd_mul_left 2 m 1
        _ = 2 := by simp

/-- Multiplication by half the modulus on `ZMod (2m)` has fibers of size
at most `m`. -/
theorem natCard_m_nsmulZModFiber_le_m
    (m : ℕ) (hm : 0 < m) (t : ZMod (2 * m)) :
    Nat.card (NsmulZModFiber (2 * m) m t) ≤ m := by
  calc
    Nat.card (NsmulZModFiber (2 * m) m t) ≤
        (2 * m).gcd m :=
      natCard_nsmulZModFiber_le_gcd
        (2 * m) m (by omega) t
    _ = m := by
      calc
        (2 * m).gcd m = (2 * m).gcd (1 * m) := by rw [one_mul]
        _ = (2 : ℕ).gcd 1 * m := Nat.gcd_mul_right 2 m 1
        _ = m := by simp

/-- Square fibers are preserved by a group equivalence. -/
def squareFiberMulEquiv
    {G H : Type*} [Group G] [Group H]
    (equiv : G ≃* H) (a : G) :
    SquareFiber G a ≃ SquareFiber H (equiv a) where
  toFun x := ⟨equiv x.1, by
    simpa using congrArg equiv x.2⟩
  invFun x := ⟨equiv.symm x.1, by
    apply equiv.injective
    simpa using x.2⟩
  left_inv x := Subtype.ext (equiv.symm_apply_apply x.1)
  right_inv x := Subtype.ext (equiv.apply_symm_apply x.1)

namespace DihedralGroup

/-- The square-one fiber in a dihedral group of rotation order `4k`
has at most `4k+2` elements. -/
theorem natCard_squareFiber_one_le
    (k : ℕ) (hk : 0 < k) :
    Nat.card (SquareFiber (DihedralGroup (4 * k)) 1) ≤
      4 * k + 2 := by
  letI : NeZero (4 * k) := ⟨by omega⟩
  let Target :=
    NsmulZModFiber (4 * k) 2 0 ⊕ ZMod (4 * k)
  let encode :
      SquareFiber (DihedralGroup (4 * k)) 1 → Target :=
    fun x ↦ match hx : x.1 with
      | .r i => Sum.inl ⟨i, by
          have hsq := x.2
          rw [hx, pow_two, DihedralGroup.r_mul_r,
            DihedralGroup.one_def] at hsq
          have hi : i + i = 0 := DihedralGroup.r.inj hsq
          rw [two_nsmul]
          exact hi⟩
      | .sr i => Sum.inr i
  let decode : Target → DihedralGroup (4 * k)
    | Sum.inl i => .r i.1
    | Sum.inr i => .sr i
  have hrecover :
      ∀ x : SquareFiber (DihedralGroup (4 * k)) 1,
        decode (encode x) = x.1 := by
    rintro ⟨x, hx⟩
    cases x <;> rfl
  have hinjective : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    rw [← hrecover x, ← hrecover y, hxy]
  calc
    Nat.card (SquareFiber (DihedralGroup (4 * k)) 1) ≤
        Nat.card Target :=
      Nat.card_le_card_of_injective encode hinjective
    _ = Nat.card (NsmulZModFiber (4 * k) 2 0) +
          Nat.card (ZMod (4 * k)) := Nat.card_sum
    _ ≤ 2 + 4 * k := by
      exact Nat.add_le_add
        (calc
          Nat.card (NsmulZModFiber (4 * k) 2 0) ≤
              (4 * k).gcd 2 :=
            natCard_nsmulZModFiber_le_gcd
              (4 * k) 2 (by omega) 0
          _ = 2 := by
            calc
              (4 * k).gcd 2 =
                  (2 * (2 * k)).gcd (2 * 1) := by
                    rw [show 4 * k = 2 * (2 * k) by omega]
              _ = 2 * (2 * k).gcd 1 :=
                Nat.gcd_mul_left 2 (2 * k) 1
              _ = 2 := by simp)
        (le_of_eq (Nat.card_zmod (4 * k)))
    _ = 4 * k + 2 := by omega

/-- A square fiber over a nonidentity element in a dihedral group of
rotation order `4k` has at most two elements. -/
theorem natCard_squareFiber_ne_one_le_two
    (k : ℕ) (hk : 0 < k)
    (z : DihedralGroup (4 * k)) (hz : z ≠ 1) :
    Nat.card (SquareFiber (DihedralGroup (4 * k)) z) ≤ 2 := by
  letI : NeZero (4 * k) := ⟨by omega⟩
  cases hzForm : z with
  | r j =>
      let encode :
          SquareFiber (DihedralGroup (4 * k)) z →
            NsmulZModFiber (4 * k) 2 j :=
        fun x ↦ match hx : x.1 with
          | .r i => ⟨i, by
              have hsq := x.2
              rw [hx, hzForm, pow_two,
                DihedralGroup.r_mul_r] at hsq
              have hi : i + i = j :=
                DihedralGroup.r.inj hsq
              rw [two_nsmul]
              exact hi⟩
          | .sr i => False.elim <| hz <| by
              have hsq := x.2
              rw [hx, pow_two, DihedralGroup.sr_mul_sr] at hsq
              simpa using hsq.symm
      let decode :
          NsmulZModFiber (4 * k) 2 j →
            DihedralGroup (4 * k) :=
        fun i ↦ .r i.1
      have hrecover :
          ∀ x : SquareFiber (DihedralGroup (4 * k)) z,
            decode (encode x) = x.1 := by
        rintro ⟨x, hx⟩
        cases x with
        | r i => rfl
        | sr i =>
            exfalso
            apply hz
            rw [pow_two, DihedralGroup.sr_mul_sr] at hx
            simpa using hx.symm
      have hinjective : Function.Injective encode := by
        intro x y hxy
        apply Subtype.ext
        rw [← hrecover x, ← hrecover y, hxy]
      simpa only [hzForm] using
        (Nat.card_le_card_of_injective encode hinjective).trans
          (calc
            Nat.card (NsmulZModFiber (4 * k) 2 j) ≤
                (4 * k).gcd 2 :=
              natCard_nsmulZModFiber_le_gcd
                (4 * k) 2 (by omega) j
            _ = 2 := by
              calc
                (4 * k).gcd 2 =
                    (2 * (2 * k)).gcd (2 * 1) := by
                      rw [show 4 * k = 2 * (2 * k) by omega]
                _ = 2 * (2 * k).gcd 1 :=
                  Nat.gcd_mul_left 2 (2 * k) 1
                _ = 2 := by simp)
  | sr j =>
      have hempty :
          IsEmpty (SquareFiber (DihedralGroup (4 * k)) z) := by
        constructor
        intro x
        cases hx : x.1 <;>
          have hsq := x.2 <;>
          simp only [hx, pow_two, DihedralGroup.r_mul_r,
            DihedralGroup.sr_mul_sr, hzForm] at hsq <;>
          contradiction
      letI := hempty
      have hzero :
          Nat.card (SquareFiber (DihedralGroup (4 * k)) z) = 0 :=
        Nat.card_of_isEmpty
      rw [← hzForm]
      rw [hzero]
      omega

end DihedralGroup

namespace IsSemidihedralPresentation

variable {P : Type*} [Group P] {k : ℕ}

/-- The square of a rotation in the semidihedral normal form. -/
private theorem rotation_sq
    (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k)) :
    h.rotation i ^ 2 = h.rotation (2 • i) := by
  rw [pow_two, rotation_mul_rotation_apply, two_nsmul]

/-- The square of a coset normal form in a semidihedral presentation. -/
private theorem coset_sq
    (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k)) :
    h.coset i ^ 2 = h.rotation ((4 * k) • i) := by
  rw [pow_two, coset_mul_coset_apply]
  apply congrArg h.rotation
  dsimp only [semidihedralTwist]
  norm_num [nsmul_eq_mul, Nat.cast_mul]
  ring

/-- A square fiber over a rotation in a semidihedral normal form has at
most `4k+2` elements. -/
private theorem natCard_squareFiber_rotation_le
    (h : IsSemidihedralPresentation P k)
    (hk : 0 < k) (j : ZMod (8 * k)) :
    Nat.card (SquareFiber P (h.rotation j)) ≤ 4 * k + 2 := by
  letI : NeZero (8 * k) := ⟨by omega⟩
  let Target :=
    {s : ZMod (8 * k) ⊕ ZMod (8 * k) //
      match s with
      | .inl i => 2 • i = j
      | .inr i => (4 * k) • i = j}
  let encode : SquareFiber P (h.rotation j) → Target :=
    fun x ↦ ⟨h.normalForm.symm x.1, by
      cases hx : h.normalForm.symm x.1 with
      | inl i =>
          change 2 • i = j
          have hxForm : x.1 = h.rotation i := by
            simpa [rotation] using congrArg h.normalForm hx
          have hsq := x.2
          rw [hxForm, rotation_sq] at hsq
          exact h.rotation_injective hsq
      | inr i =>
          change (4 * k) • i = j
          have hxForm : x.1 = h.coset i := by
            simpa [coset] using congrArg h.normalForm hx
          have hsq := x.2
          rw [hxForm, coset_sq] at hsq
          exact h.rotation_injective hsq⟩
  have hinjective : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply h.normalForm.symm.injective
    exact congrArg Subtype.val hxy
  let targetEquiv :
      Target ≃
        (NsmulZModFiber (8 * k) 2 j ⊕
          NsmulZModFiber (8 * k) (4 * k) j) := {
    toFun s := match s with
      | ⟨.inl i, hi⟩ => Sum.inl ⟨i, hi⟩
      | ⟨.inr i, hi⟩ => Sum.inr ⟨i, hi⟩
    invFun s := match s with
      | .inl i => ⟨.inl i.1, i.2⟩
      | .inr i => ⟨.inr i.1, i.2⟩
    left_inv s := by
      rcases s with ⟨s, hs⟩
      cases s <;> rfl
    right_inv s := by
      cases s <;> rfl
  }
  calc
    Nat.card (SquareFiber P (h.rotation j)) ≤ Nat.card Target :=
      Nat.card_le_card_of_injective encode hinjective
    _ = Nat.card
          (NsmulZModFiber (8 * k) 2 j ⊕
            NsmulZModFiber (8 * k) (4 * k) j) :=
      Nat.card_congr targetEquiv
    _ = Nat.card (NsmulZModFiber (8 * k) 2 j) +
          Nat.card (NsmulZModFiber (8 * k) (4 * k) j) :=
      Nat.card_sum
    _ ≤ 2 + 4 * k := by
      apply Nat.add_le_add
      · calc
          Nat.card (NsmulZModFiber (8 * k) 2 j) ≤
              (8 * k).gcd 2 :=
            natCard_nsmulZModFiber_le_gcd
              (8 * k) 2 (by omega) j
          _ = 2 := by
            calc
              (8 * k).gcd 2 =
                  (2 * (4 * k)).gcd (2 * 1) := by
                    rw [show 8 * k = 2 * (4 * k) by omega]
              _ = 2 * (4 * k).gcd 1 :=
                Nat.gcd_mul_left 2 (4 * k) 1
              _ = 2 := by simp
      · calc
          Nat.card (NsmulZModFiber (8 * k) (4 * k) j) ≤
              (8 * k).gcd (4 * k) :=
            natCard_nsmulZModFiber_le_gcd
              (8 * k) (4 * k) (by omega) j
          _ = 4 * k := by
            calc
              (8 * k).gcd (4 * k) =
                  (2 * (4 * k)).gcd (1 * (4 * k)) := by
                    rw [show 8 * k = 2 * (4 * k) by omega,
                      one_mul]
              _ = (2 : ℕ).gcd 1 * (4 * k) :=
                Nat.gcd_mul_right 2 (4 * k) 1
              _ = 4 * k := by simp
    _ = 4 * k + 2 := by omega

/-- Every square fiber in a semidihedral normal form has at most
`4k+2` elements. -/
theorem natCard_squareFiber_le
    (h : IsSemidihedralPresentation P k)
    (hk : 0 < k) (z : P) :
    Nat.card (SquareFiber P z) ≤ 4 * k + 2 := by
  letI : NeZero (8 * k) := ⟨by omega⟩
  cases hz : h.normalForm.symm z with
  | inl j =>
      have hzForm : z = h.rotation j := by
        simpa [rotation] using congrArg h.normalForm hz
      rw [hzForm]
      exact h.natCard_squareFiber_rotation_le hk j
  | inr j =>
      have hzForm : z = h.coset j := by
        simpa [coset] using congrArg h.normalForm hz
      have hempty : IsEmpty (SquareFiber P z) := by
        constructor
        intro x
        cases hx : h.normalForm.symm x.1 with
        | inl i =>
            have hxForm : x.1 = h.rotation i := by
              simpa [rotation] using congrArg h.normalForm hx
            have hsq := x.2
            rw [hxForm, rotation_sq, hzForm] at hsq
            exact h.rotation_ne_coset _ _ hsq
        | inr i =>
            have hxForm : x.1 = h.coset i := by
              simpa [coset] using congrArg h.normalForm hx
            have hsq := x.2
            rw [hxForm, coset_sq, hzForm] at hsq
            exact h.rotation_ne_coset _ _ hsq
      letI := hempty
      rw [Nat.card_of_isEmpty]
      omega

end IsSemidihedralPresentation

namespace QuaternionGroup

/-- The square-one fiber in a generalized quaternion group has at most
two elements. -/
theorem natCard_squareFiber_one_le
    (n : ℕ) (hn : 0 < n) :
    Nat.card (SquareFiber (QuaternionGroup n) 1) ≤ 2 := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hnCast :
      ((n : ℕ) : ZMod (2 * n)) ≠ 0 := by
    intro hz
    have hval := congrArg ZMod.val hz
    rw [ZMod.val_natCast, ZMod.val_zero] at hval
    have hnlt : n < 2 * n := by omega
    rw [Nat.mod_eq_of_lt hnlt] at hval
    omega
  let encode :
      SquareFiber (QuaternionGroup n) 1 →
        NsmulZModFiber (2 * n) 2 0 :=
    fun x ↦ match hx : x.1 with
      | .a i => ⟨i, by
          have hsq := x.2
          rw [hx, pow_two, QuaternionGroup.a_mul_a,
            QuaternionGroup.one_def] at hsq
          have hi : i + i = 0 := QuaternionGroup.a.inj hsq
          rw [two_nsmul]
          exact hi⟩
      | .xa i => False.elim <| hnCast <| by
          have hsq := x.2
          rw [hx, QuaternionGroup.xa_sq,
            QuaternionGroup.one_def] at hsq
          exact QuaternionGroup.a.inj hsq
  let decode :
      NsmulZModFiber (2 * n) 2 0 → QuaternionGroup n :=
    fun i ↦ .a i.1
  have hrecover :
      ∀ x : SquareFiber (QuaternionGroup n) 1,
        decode (encode x) = x.1 := by
    rintro ⟨x, hxSquare⟩
    cases x with
    | a i => rfl
    | xa i =>
        exfalso
        apply hnCast
        rw [QuaternionGroup.xa_sq,
          QuaternionGroup.one_def] at hxSquare
        exact QuaternionGroup.a.inj hxSquare
  have hinjective : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    rw [← hrecover x, ← hrecover y, hxy]
  exact
    (Nat.card_le_card_of_injective encode hinjective).trans
      (natCard_two_nsmulZModFiber_le_two n hn 0)

/-- A square fiber over a rotation in a generalized quaternion group has
at most `2n+2` elements. -/
private theorem natCard_squareFiber_a_le
    (n : ℕ) (hn : 0 < n) (j : ZMod (2 * n)) :
    Nat.card (SquareFiber (QuaternionGroup n) (.a j)) ≤
      2 * n + 2 := by
  letI : NeZero n := ⟨hn.ne'⟩
  let Target :=
    NsmulZModFiber (2 * n) 2 j ⊕ ZMod (2 * n)
  let encode :
      SquareFiber (QuaternionGroup n) (.a j) → Target :=
    fun x ↦ match hx : x.1 with
      | .a i => Sum.inl ⟨i, by
          have hsq := x.2
          rw [hx, pow_two, QuaternionGroup.a_mul_a] at hsq
          have hi : i + i = j := QuaternionGroup.a.inj hsq
          rw [two_nsmul]
          exact hi⟩
      | .xa i => Sum.inr i
  let decode : Target → QuaternionGroup n
    | Sum.inl i => .a i.1
    | Sum.inr i => .xa i
  have hrecover :
      ∀ x : SquareFiber (QuaternionGroup n) (.a j),
        decode (encode x) = x.1 := by
    rintro ⟨x, hxSquare⟩
    cases x <;> rfl
  have hinjective : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    rw [← hrecover x, ← hrecover y, hxy]
  calc
    Nat.card (SquareFiber (QuaternionGroup n) (.a j)) ≤
        Nat.card Target :=
      Nat.card_le_card_of_injective encode hinjective
    _ = Nat.card (NsmulZModFiber (2 * n) 2 j) +
          Nat.card (ZMod (2 * n)) := Nat.card_sum
    _ ≤ 2 + 2 * n := by
      exact Nat.add_le_add
        (natCard_two_nsmulZModFiber_le_two n hn j)
        (le_of_eq (Nat.card_zmod (2 * n)))
    _ = 2 * n + 2 := by omega

/-- Every square fiber in a generalized quaternion group has at most
`2n+2` elements. -/
theorem natCard_squareFiber_le
    (n : ℕ) (hn : 0 < n) (z : QuaternionGroup n) :
    Nat.card (SquareFiber (QuaternionGroup n) z) ≤
      2 * n + 2 := by
  letI : NeZero n := ⟨hn.ne'⟩
  cases hzForm : z with
  | a j =>
      simpa only [hzForm] using
        QuaternionGroup.natCard_squareFiber_a_le n hn j
  | xa j =>
      have hempty :
          IsEmpty
            (SquareFiber (QuaternionGroup n)
              (QuaternionGroup.xa j)) := by
        constructor
        intro x
        cases hx : x.1 with
        | a i =>
            have hsq := x.2
            rw [hx, pow_two, QuaternionGroup.a_mul_a] at hsq
            contradiction
        | xa i =>
            have hsq := x.2
            rw [hx, QuaternionGroup.xa_sq] at hsq
            contradiction
      letI := hempty
      rw [Nat.card_of_isEmpty]
      omega

end QuaternionGroup

namespace BergerMaximalClassHead

variable {H : Type*} [Group H] [Finite H]

/-- The maximal-class head square-fiber bounds, proved from the three
normal forms.  Nontriviality is needed only in the dihedral row, whose
central square fiber has the sharper bound `2`. -/
theorem squareCountData
    (head : BergerMaximalClassHead H)
    (z : Subgroup.center H) (hz : z ≠ 1) :
    head.SquareCountData z := by
  cases head with
  | dihedral k hk equiv =>
      have hkPos : 0 < k := by omega
      refine ⟨?_, ?_⟩
      · have hcard :
            Nat.card (SquareFiber H 1) =
              Nat.card
                (SquareFiber (DihedralGroup (4 * k)) 1) := by
          calc
            Nat.card (SquareFiber H 1) =
                Nat.card
                  (SquareFiber (DihedralGroup (4 * k))
                    (equiv 1)) :=
              Nat.card_congr (squareFiberMulEquiv equiv 1)
            _ = Nat.card
                  (SquareFiber (DihedralGroup (4 * k)) 1) := by
              rw [equiv.map_one]
        simpa only [squareOneCount, rotationOrder, hcard] using
          DihedralGroup.natCard_squareFiber_one_le k hkPos
      · have hzImage : equiv z.1 ≠ 1 := by
          intro hzImage
          apply hz
          apply Subtype.ext
          apply equiv.injective
          simpa using hzImage
        have hcard :
            Nat.card (SquareFiber H z.1) =
              Nat.card
                (SquareFiber (DihedralGroup (4 * k))
                  (equiv z.1)) :=
          Nat.card_congr (squareFiberMulEquiv equiv z.1)
        simpa only [squareCentralCount, rotationOrder, hcard] using
          DihedralGroup.natCard_squareFiber_ne_one_le_two
            k hkPos (equiv z.1) hzImage
  | semidihedral k hk presentation =>
      have hdiv : 8 * k / 2 = 4 * k := by omega
      refine ⟨?_, ?_⟩
      · simpa only [squareOneCount, rotationOrder, hdiv] using
          presentation.natCard_squareFiber_le hk (1 : H)
      · simpa only [squareCentralCount, rotationOrder, hdiv] using
          presentation.natCard_squareFiber_le hk z.1
  | generalizedQuaternion n hn equiv =>
      have hnPos : 0 < n := by omega
      refine ⟨?_, ?_⟩
      · have hcard :
            Nat.card (SquareFiber H 1) =
              Nat.card (SquareFiber (QuaternionGroup n) 1) := by
          calc
            Nat.card (SquareFiber H 1) =
                Nat.card
                  (SquareFiber (QuaternionGroup n) (equiv 1)) :=
              Nat.card_congr (squareFiberMulEquiv equiv 1)
            _ = Nat.card (SquareFiber (QuaternionGroup n) 1) := by
              rw [equiv.map_one]
        simpa only [squareOneCount, rotationOrder, hcard] using
          QuaternionGroup.natCard_squareFiber_one_le n hnPos
      · have hcard :
            Nat.card (SquareFiber H z.1) =
              Nat.card
                (SquareFiber (QuaternionGroup n) (equiv z.1)) :=
          Nat.card_congr (squareFiberMulEquiv equiv z.1)
        simpa only [squareCentralCount, rotationOrder, hcard] using
          QuaternionGroup.natCard_squareFiber_le
            n hnPos (equiv z.1)

end BergerMaximalClassHead

namespace BergerMixedCentralProductData

variable {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Fintype P]

/-- After the head normal-form computation, the mixed active-count
bookkeeping depends only on the sign-free extraspecial square count. -/
theorem active_card_le_countingEnvelope_of_extraSquareData
    (data : BergerMixedCentralProductData P)
    (e : ℕ)
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    (activePrimeOrderElements 2 P).card ≤
      data.head.countingEnvelope e := by
  apply data.active_card_le_countingEnvelope P e extra
  exact data.head.squareCountData
    (data.headCentralInvolution extra)
    (data.headCentralInvolution_ne_one extra)

end BergerMixedCentralProductData

end LisiSabatini
