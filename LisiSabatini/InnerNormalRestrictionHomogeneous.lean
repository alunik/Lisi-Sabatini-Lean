import LisiSabatini.NormalRestrictionSemisimple

/-!
# Homogeneity of inner normal restrictions

Let `H ◁ G`.  Clifford theory says that the simple constituents of the
restriction of an irreducible `G`-module form one `G`-orbit.  If the
conjugation action of `G` on `H` is inner, that orbit has only one
isomorphism type, so the restriction is homogeneous.

The theorem below proves precisely this elementary form.  It is useful for
an internal central product `G = EH`: if `E` and `H` commute, then every
ambient conjugation on `E` is already conjugation by an element of `E`.
-/

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

universe uK uG uV

namespace Representation

variable {k : Type uK} {G : Type uG} {V : Type uV}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Ambient conjugation on `H` is inner, in the convenient equivalent form
that every ambient element has the same conjugation action as some element
of `H`.  Equivalently, after multiplying by that element of `H`, one obtains
an element centralizing `H`. -/
def HasInnerConjugationOn
    (H : Subgroup G) : Prop :=
  ∀ g : G, ∃ h : H, ∀ x : H, Commute ((h : G)⁻¹ * g) (x : G)

namespace HasInnerConjugationOn

/-- Inner ambient conjugation in particular makes the subgroup normal. -/
theorem normal
    {H : Subgroup G}
    (hinner : HasInnerConjugationOn H) :
    H.Normal := by
  constructor
  intro n hn g
  obtain ⟨h, hh⟩ := hinner g
  let a : G := (h : G)⁻¹ * g
  let x : H := ⟨n, hn⟩
  have hag : (h : G) * a = g := by
    dsimp only [a]
    group
  have hcomm : a * n = n * a := by
    exact (hh x).eq
  have hconj :
    g * n * g⁻¹ =
      (h : G) * n * (h : G)⁻¹ := by
    calc
      g * n * g⁻¹ =
          (h : G) * a * n * a⁻¹ * (h : G)⁻¹ := by
        rw [← hag]
        group
      _ = (h : G) * (a * n) * a⁻¹ * (h : G)⁻¹ := by
        group
      _ = (h : G) * (n * a) * a⁻¹ * (h : G)⁻¹ := by
        rw [hcomm]
      _ = (h : G) * n * (h : G)⁻¹ := by
        group
  rw [hconj]
  exact
    H.mul_mem
      (H.mul_mem h.property hn)
      (H.inv_mem h.property)

end HasInnerConjugationOn

variable (rho : Representation k G V)
variable (H : Subgroup G)

private abbrev restrictedRepresentation :
    Representation k H V :=
  rho.comp H.subtype

/-- An ambient operator centralizing `H` is an endomorphism of the
restricted `k[H]`-module. -/
private def centralizingRestrictedEnd
    (a : G) (ha : ∀ x : H, Commute a (x : G)) :
    Module.End k[H] (restrictedRepresentation rho H).asModule where
  toFun u :=
    (restrictedRepresentation rho H).asModuleEquiv.symm
      (rho a ((restrictedRepresentation rho H).asModuleEquiv u))
  map_add' u v := by
    simp
  map_smul' c u := by
    apply (restrictedRepresentation rho H).asModuleEquiv.injective
    rw [(restrictedRepresentation rho H).asModuleEquiv_map_smul]
    change
      rho a
          ((restrictedRepresentation rho H).asAlgebraHom c
            ((restrictedRepresentation rho H).asModuleEquiv u)) =
        (restrictedRepresentation rho H).asAlgebraHom c
          (rho a ((restrictedRepresentation rho H).asModuleEquiv u))
    induction c using MonoidAlgebra.induction_on with
    | hM x =>
        simp only [Representation.asAlgebraHom_of]
        change
          rho a (rho (x : G)
            ((restrictedRepresentation rho H).asModuleEquiv u)) =
          rho (x : G)
            (rho a ((restrictedRepresentation rho H).asModuleEquiv u))
        simp only [← Module.End.mul_apply, ← map_mul]
        exact
          congrArg
            (fun T : Module.End k V ↦
              T ((restrictedRepresentation rho H).asModuleEquiv u))
            (congrArg rho (ha x).eq)
    | hadd c d hc hd =>
        simp only [map_add, LinearMap.add_apply]
        exact congrArg₂ (· + ·) hc hd
    | hsmul c d hd =>
        simp only [map_smul, LinearMap.smul_apply]
        exact congrArg (fun z ↦ c • z) hd

/-- Restrict an endomorphism of the ambient group module to an
endomorphism of the subgroup module, transporting through the two
representation-module type synonyms. -/
private def restrictAmbientModuleEnd
    (F : Module.End k[G] rho.asModule) :
    Module.End k[H] (restrictedRepresentation rho H).asModule where
  toFun u :=
    (restrictedRepresentation rho H).asModuleEquiv.symm
      (rho.asModuleEquiv
        (F
          (rho.asModuleEquiv.symm
            ((restrictedRepresentation rho H).asModuleEquiv u))))
  map_add' u v := by
    simp
  map_smul' c u := by
    apply (restrictedRepresentation rho H).asModuleEquiv.injective
    rw [(restrictedRepresentation rho H).asModuleEquiv_map_smul]
    simp only [LinearEquiv.apply_symm_apply, RingHom.id_apply]
    induction c using MonoidAlgebra.induction_on with
    | hM x =>
        simp only [Representation.asAlgebraHom_of]
        let w :=
          rho.asModuleEquiv.symm
            ((restrictedRepresentation rho H).asModuleEquiv u)
        have hF :=
          F.map_smul (MonoidAlgebra.of k G (x : G)) w
        have hFv := congrArg rho.asModuleEquiv hF
        simpa [restrictedRepresentation, w] using hFv
    | hadd c d hc hd =>
        simp only [map_add, LinearMap.add_apply, add_smul]
        exact congrArg₂ (· + ·) hc hd
    | hsmul c d hd =>
        simp only [map_smul, LinearMap.smul_apply, smul_assoc,
          LinearMap.map_smul_of_tower]
        exact congrArg (fun z ↦ c • z) hd

/-- The inner-normal-restriction lemma for an ambient homogeneous module.

Semisimplicity of the restriction is made explicit because it may come
either from the irreducible normal-restriction theorem or, in the
Hall--Berger application, directly from cross-characteristic Maschke.
The isotypicity argument needs no irreducibility: a fully invariant
submodule for the restricted module is stable under ambient conjugation
and under every ambient module endomorphism, hence is fully invariant in
the ambient homogeneous module and must be zero or top. -/
theorem isHomogeneous_restrict_of_homogeneous_of_innerConjugation
    (hhom : IsHomogeneous rho)
    (hsemi :
      IsSemisimpleModule k[H]
        (restrictedRepresentation rho H).asModule)
    (hinner : HasInnerConjugationOn H) :
    IsHomogeneous (restrictedRepresentation rho H) := by
  let sigma := restrictedRepresentation rho H
  letI : IsSemisimpleModule k[H] sigma.asModule := hsemi
  letI : IsSemisimpleModule k[G] rho.asModule := hhom.1
  refine ⟨inferInstance, ?_⟩
  rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top]
  intro C hC
  let Wsub : Submodule k V :=
    (C.restrictScalars k).map sigma.asModuleEquiv.toLinearMap
  have hWstable : Wsub ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro g v hv
    obtain ⟨h, hh⟩ := hinner g
    let a : G := (h : G)⁻¹ * g
    let f : Module.End k[H] sigma.asModule :=
      centralizingRestrictedEnd rho H a hh
    rcases hv with ⟨u, hu, rfl⟩
    have hfu : f u ∈ C := hC f hu
    have hhfu :
        MonoidAlgebra.of k H h • f u ∈ C :=
      C.smul_mem (MonoidAlgebra.of k H h) hfu
    refine ⟨MonoidAlgebra.of k H h • f u, hhfu, ?_⟩
    change
      (restrictedRepresentation rho H).asModuleEquiv
          (MonoidAlgebra.of k H h • f u) =
        rho g ((restrictedRepresentation rho H).asModuleEquiv u)
    rw [(restrictedRepresentation rho H).asModuleEquiv_map_smul]
    simp only [Representation.asAlgebraHom_of]
    change
      rho (h : G)
          (rho a ((restrictedRepresentation rho H).asModuleEquiv u)) =
        rho g ((restrictedRepresentation rho H).asModuleEquiv u)
    simp only [← Module.End.mul_apply, ← map_mul]
    have hha : (h : G) * a = g := by
      dsimp only [a]
      group
    exact
      congrArg
        (fun T : Module.End k V ↦
          T ((restrictedRepresentation rho H).asModuleEquiv u))
        (congrArg rho hha)
  let W : rho.invtSubmodule := ⟨Wsub, hWstable⟩
  let CG : Submodule k[G] rho.asModule :=
    Representation.mapSubmodule rho W
  have hCGfully : CG.IsFullyInvariant := by
    intro F z hz
    change z ∈
      (Wsub : Submodule k V).toAddSubmonoid.map
        rho.asModuleEquiv.symm at hz
    rcases hz with ⟨v, hv, rfl⟩
    rcases hv with ⟨u, hu, rfl⟩
    let f : Module.End k[H] sigma.asModule :=
      restrictAmbientModuleEnd rho H F
    have hfu : f u ∈ C := hC f hu
    change
      F (rho.asModuleEquiv.symm (sigma.asModuleEquiv u)) ∈
        (Wsub : Submodule k V).toAddSubmonoid.map
          rho.asModuleEquiv.symm
    refine
      ⟨sigma.asModuleEquiv (f u),
        ⟨f u, hfu, rfl⟩, ?_⟩
    change
      rho.asModuleEquiv.symm
          (rho.asModuleEquiv
            (F
              (rho.asModuleEquiv.symm
                (sigma.asModuleEquiv u)))) =
        F (rho.asModuleEquiv.symm (sigma.asModuleEquiv u))
    exact rho.asModuleEquiv.symm_apply_apply _
  have hCG :
      CG = ⊥ ∨ CG = ⊤ :=
    (isIsotypic_iff_isFullyInvariant_imp_bot_or_top.mp hhom.2)
      CG hCGfully
  rcases hCG with hbot | htop
  · left
    have hWbot : Wsub = ⊥ := by
      have h :=
        congrArg
          (fun X : Submodule k[G] rho.asModule ↦
            (Representation.mapSubmodule rho).symm X)
          hbot
      have hW : W = ⊥ := by simpa [CG] using h
      exact congrArg Subtype.val hW
    change
      (C.restrictScalars k).map
          sigma.asModuleEquiv.toLinearMap = ⊥ at hWbot
    rw [Submodule.map_eq_bot_iff] at hWbot
    exact
      (Submodule.restrictScalars_eq_bot_iff
        k k[H] sigma.asModule).mp hWbot
  · right
    have hWtop : Wsub = ⊤ := by
      have h :=
        congrArg
          (fun X : Submodule k[G] rho.asModule ↦
            (Representation.mapSubmodule rho).symm X)
          htop
      have hW : W = ⊤ := by simpa [CG] using h
      exact congrArg Subtype.val hW
    change
      (C.restrictScalars k).map
          sigma.asModuleEquiv.toLinearMap = ⊤ at hWtop
    rw [Submodule.map_eq_top_iff] at hWtop
    exact
      (Submodule.restrictScalars_eq_top_iff
        k k[H] sigma.asModule).mp hWtop

/-- **Inner-normal-restriction lemma.**  If `rho` is a finite-dimensional
irreducible representation and every ambient conjugation on `H` is inner,
then the restriction of `rho` to `H` is homogeneous.

Semisimplicity is the modular Clifford socle theorem.  For isotypicity,
take a fully invariant `k[H]`-submodule.  An ambient operator is an
`H`-operator followed by an operator centralizing `H`; full invariance
therefore makes the corresponding subspace `G`-stable.  Irreducibility
forces it to be zero or the whole space. -/
theorem isHomogeneous_restrict_of_irreducible_of_innerConjugation
    [FiniteDimensional k V]
    [H.Normal]
    (hirr : rho.IsIrreducible)
    (hinner : HasInnerConjugationOn H) :
    IsHomogeneous (restrictedRepresentation rho H) := by
  let sigma := restrictedRepresentation rho H
  letI : IsSemisimpleModule k[H] sigma.asModule :=
    isSemisimpleModule_normalRestriction rho H hirr
  refine ⟨inferInstance, ?_⟩
  rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top]
  intro C hC
  let Wsub : Submodule k V :=
    (C.restrictScalars k).map sigma.asModuleEquiv.toLinearMap
  have hWstable : Wsub ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro g v hv
    obtain ⟨h, hh⟩ := hinner g
    let a : G := (h : G)⁻¹ * g
    let f : Module.End k[H] sigma.asModule :=
      centralizingRestrictedEnd rho H a hh
    rcases hv with ⟨u, hu, rfl⟩
    have hfu : f u ∈ C := hC f hu
    have hhfu :
        MonoidAlgebra.of k H h • f u ∈ C :=
      C.smul_mem (MonoidAlgebra.of k H h) hfu
    refine ⟨MonoidAlgebra.of k H h • f u, hhfu, ?_⟩
    change
      (restrictedRepresentation rho H).asModuleEquiv
          (MonoidAlgebra.of k H h • f u) =
        rho g ((restrictedRepresentation rho H).asModuleEquiv u)
    rw [(restrictedRepresentation rho H).asModuleEquiv_map_smul]
    simp only [Representation.asAlgebraHom_of]
    change
      rho (h : G)
          (rho a ((restrictedRepresentation rho H).asModuleEquiv u)) =
        rho g ((restrictedRepresentation rho H).asModuleEquiv u)
    simp only [← Module.End.mul_apply, ← map_mul]
    have hha : (h : G) * a = g := by
      dsimp only [a]
      group
    exact
      congrArg
        (fun T : Module.End k V ↦
          T ((restrictedRepresentation rho H).asModuleEquiv u))
        (congrArg rho hha)
  let W : rho.invtSubmodule := ⟨Wsub, hWstable⟩
  letI : IsSimpleModule k[G] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hirr
  rcases eq_bot_or_eq_top (Representation.mapSubmodule rho W) with
      hbot | htop
  · left
    have hWbot : Wsub = ⊥ := by
      have h :=
        congrArg
          (fun X : Submodule k[G] rho.asModule ↦
            (Representation.mapSubmodule rho).symm X)
          hbot
      have hW : W = ⊥ := by simpa using h
      exact congrArg Subtype.val hW
    change
      (C.restrictScalars k).map
          sigma.asModuleEquiv.toLinearMap = ⊥ at hWbot
    rw [Submodule.map_eq_bot_iff] at hWbot
    exact
      (Submodule.restrictScalars_eq_bot_iff
        k k[H] sigma.asModule).mp hWbot
  · right
    have hWtop : Wsub = ⊤ := by
      have h :=
        congrArg
          (fun X : Submodule k[G] rho.asModule ↦
            (Representation.mapSubmodule rho).symm X)
          htop
      have hW : W = ⊤ := by simpa using h
      exact congrArg Subtype.val hW
    change
      (C.restrictScalars k).map
          sigma.asModuleEquiv.toLinearMap = ⊤ at hWtop
    rw [Submodule.map_eq_top_iff] at hWtop
    exact
      (Submodule.restrictScalars_eq_top_iff
        k k[H] sigma.asModule).mp hWtop

end Representation

end LisiSabatini
