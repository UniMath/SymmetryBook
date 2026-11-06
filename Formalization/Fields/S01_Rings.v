(** * Section 13.1 Rings, abstract and concrete

    Part of Chapter 13 ([fields.tex]); see [Fields.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    Subsections 13.1.1 and 13.1.2:
    - Definitions [def:abstractring] and [def:typering]: [DistrLaws]
      ([ring:ldistr-law], [ring:rdistr-law]) and the book's [Σ]-type
      [AbsRing] (the book's [Ring]), with projections [ar_grp],
      [ar_one], [ar_mul], ..., the monoid [ar_monoid], and
      [ar_isNontrivial], [ar_isComm], [AbsCommRing].
    - Exercise [xca:ring-group-abelian] ([xca_ring_group_abelian]),
      following the hint: expand [(a+1)·(b+1)] in two ways and cancel.
    - Definition [def:ringhom] ([AbsRingHom], [AbsRingHom_monoid]).
      Example [exa:ring-Z-polynomials] is [TBD] in the book.
    - Definitions [def:mixring] and [def:typemixring]: [RingProps]
      ([mixring:unit-laws], [mixring:lr-coherence-law],
      [mixring:assoc-law]), [MixRing], [MixCommRing],
      [mr_isNontrivial].  The associativity law [ℓ ∘ r = r ∘ ℓ] is read
      pointwise, [ℓ_g ∘ r_h = r_h ∘ ℓ_g] in [Hom(R,R)].
    - The example of the integers: [ℓ_g = r_g :≡ veG g] (Section 4.4),
      [Z_mixring], [Z_mixcommring], non-trivial since [loop ≠ refl];
      coherence ([Z_coh]) is [g^n = loop^{mn} = h^m] for [g = loop^m],
      [h = loop^n]; associativity follows from coherence via [Znatural]
      since homomorphisms out of [ℤ] are determined by the image of
      [loop] ([Hom_ZZ_path]).
    - Exercise [xca:Rmixring->URabstring] ([xca_Rmixring_URabstring]):
      [USym R] with [abstr(R)] and [g·h :≡ (USym ℓ_g)(h)]; the
      distributive laws are [USymf_comp] (with coherence on the right),
      associativity is the associativity law via [USym_compose]; hence
      [abstr(R)] is abelian ([mr_grp_abelian]).

    Subsection "Move to a better place (Ch. 11 or 2)":
    - [Hpt f g] is the type [H(f,g)] of [con:identity-ptd-maps]; we use
      [ptw_*] in the form of [xca:identity-ptd-maps] ([ptw_star_ind],
      which computes on [refl]) and show it is an equivalence
      ([ptw_ind_eqv]: [Σ_g H(f,g)] is contractible by [ptw_star]);
      [pmap_path] identifies pointed maps by a pointed homotopy.
    - Definition [def:ptd-homotopy-compo] ([ptw_comp]) and construction
      [con:ptd-homotopy-compo] ([con_ptd_homotopy_compo]).
    - Definition [def:cst-ptd] ([cst_ptd]; [cst_path p] is the path
      [(p, ρ_p)] in [Σ_x (pt_B = x)]); remark [rem:loops-at-ptd-cst]
      ([ptwc : Ω(X →* Y) ≃ (X →* ΩY)]).
    - Construction [con:Id-(B->*A)] ([con_Id_ptd]), exercise
      [xca:ev-section-loopsA] ([rho_r], [i_beta],
      [xca_ev_section_loopsA]), construction [con:ev-section-loopsA]
      ([s_loops], [con_ev_section_loopsA]) and corollary
      [cor:Id-(B->*loopsA)] ([cor_Id_ptd_loops]).
    - Definition [def:O-functor] ([OO], [OO_f], [OO_pt]) and exercise
      [xca:O-functor] ([OO_pid], [OO_pcomp], [OO_pt_ptw]).
    - Remark [rem:pointing-ev]: [evpt : O A →* ΩA], pointed by
      [eps_ev loop].
    - Construction [con:Omega-O]: [con_Omega_O] (via [iota], [iota_gen],
      [iota_coh], as in the book); the equivalence [e] ([e_OmegaO],
      obtained by transport along the paths [OA = ΩA] of the pointed
      equivalences [ev], characterized by [ev_B ∘ e(φ) = φ ∘ ev_A],
      [e_OmegaO_char]) and [O = e ∘ Ω] ([OO_e_loops]).
    - Construction [con:swap-ptd-doms] (implementation [TBD] in the
      book): [swap_fun], via the [Σ]-type [SwapData] of totally
      unpointed maps with both pointings and their coherence, as the
      book suggests; an involution, hence an equivalence
      ([swap_isEquiv]), pointed ([swap_ptd_pt]), with [swap_÷÷] the swap
      of arguments by definition ([swap_divdiv]).
    - Construction [con:ptw-swap-ptd-doms] ([con_ptw_swap_ptd_doms]): by
      [cor:Id-(B->*loopsA)] only the underlying maps are identified,
      using [pw_ap] ([ptw_*] is [ap] of evaluation) and [conj_ap].
    - Exercise [xca:allptd-S1-contractible] (via
      [pmap_conn_set_isContr]) and construction [con:swap-on-paths]
      ([con_swap_on_paths]).

    Example [exa:allS1*-swap]: the questions [TBD1] and [TBD2] and the
    claim [M ≃ ℤ] of that example, with [m_k ↦ k] and the reading of
    [m_k] being [kγ] (the direct [swapM] there is not related to
    [swap_fun] yet).  Not formalized yet: [rem:grpHomOK], [def:O'],
    [def:AbHomgroup], [lem:grpHomOK] and 13.1.3 Concrete rings.

    The example studies [M :≡ S¹ →* (S¹ →* B²ℤ)] and maps
    [m_k : M] given by [m_k(base) :≡ pt] and [m_k(loop) := ptw_*⁻¹(k')]
    with [k'(base) :≡ refl_pt] and [k'(loop)] the [k]-loop around
    [id_S¹].  [TBD1] asks for the relation between [m_k] and
    multiplication by [k], [TBD2] whether [swap(m_k)] is [m_k] or
    [m_{-k}].

    Forget the pointing paths and write [F(z,w) :≡ m(z)(w)] for
    [m :≡ m_1].  A pair of paths [p] in [z] and [q] in [w] gives a
    square [F(p,q)], which can be read in two ways, as a path over [p]
    or as a path over [q]:
    - z-outer: [apd] of [z ↦ ap_{F(z,-)}(q)] applied to [p]
      ([reading_z]);
    - w-outer: [apd] of [w ↦ ap_{F(-,w)}(p)] applied to [q]
      ([reading_w]).
    Both are turned into squares ([Sq t bo l r :≡ (r ⋅ t = bo ⋅ l)]) by
    the same conversion [po_sq] of paths over a path in a family of
    identity types [x ↦ (u(x) = v(x))].

    The sign:
    - [reading_w_z]: for any [F : A → B → C] and any paths [p], [q],
      [reading_w F p q = (reading_z F p q)⁻¹]: transposing a square
      inverts it.
    - [reading_w_swap]: [reading_w (swap2 F) q p ≡ reading_z F p q], so
      [reading_w (swap2 F) q p = (reading_w F p q)⁻¹].

    Bilinearity:
    - [hpaste], [vpaste]: horizontal and vertical pasting of squares;
      [reading_w_hpaste], [reading_w_vpaste]: the reading of
      [F(p' ⋅ p, q)] is the pasting of those of [F(p,q)] and [F(p',q)],
      and likewise in [q] (up to [ap_trans] on the sides).
    - For loops [p], [q] whose sides are identified with [refl]
      ([eP], [eQ]), [loops_reading F p q eP eQ] is a 2-loop at
      [F(a,b)] ([sq_2loop]).  [loops_reading_hpaste] and
      [loops_reading_vpaste]: it is a homomorphism in each variable,
      with the side identifications of composites given by [ecomp];
      [loops_reading_swap]: swapping the arguments of [F] inverts it.
    - [loop3_loop2_reading]: for [F : S¹ → S¹ → C] the 2-loop of
      [F(loop³,loop²)] is [6γ], written [((γ⋅γ)⋅(γ⋅γ))⋅(γ⋅γ)], where [γ]
      is the 2-loop of [F(loop,loop)]; [loop3_loop2_reading_z]: the
      z-outer reading, that is, [apd] of [z ↦ ap_{F(z,-)}(loop²)]
      applied to [loop³], is [(6γ)⁻¹].

    Precomposition and powers ([TBD1]):
    - [reading_w_precomp1], [reading_w_precomp2],
      [loops_reading_precomp1], [loops_reading_precomp2]: the reading
      of [F ∘ (f × id)] at [(p,q)] is that of [F] at [(ap_f(p),q)], and
      likewise in the second variable (up to [ap_comp] on the sides).
    - [loops_reading_pow1], [loops_reading_pow2]: the 2-loop of
      [F(p^n,q)] and of [F(p,q^n)] is the [n]-th power of that of
      [F(p,q)] ([ppow], with [p^{n+1} :≡ p ⋅ p^n]).
    - [loops_reading_dg1], [loops_reading_dg2]: for [F : S¹ → S¹ → C]
      and the degree [k] map [dg k] of Section 3.6 ([k : ℕ]), the 2-loop
      of [F ∘ (dg_k × id)] and of [F ∘ (id × dg_k)] at [(loop,loop)] is
      the [k]-th power of that of [F].

    How this answers [TBD2].  By definition of [m], the w-outer reading
    is the natural one: [ap_{F(-,w)}(loop) = ptw(m(loop))(w) = k'(w)], so
    the w-outer reading of [F(loop,loop)] is [ap_{k'}(loop)], the
    generator [γ] of [Ω²(B²ℤ) ≃ ℤ] (corresponding to [k = 1]); this is
    also how [M ≃ Ω²(B²ℤ)] reads off [m].  For [swap(m)] the outer
    variable is [w], so its w-outer reading is the z-outer reading of
    [m], which is [γ⁻¹] by [loops_reading_swap].  Hence
    [swap(m_1) = m_{-1}], and likewise [swap(m_k) = m_{-k}]: the twist
    on [S¹ ∧ S¹ ≃ S²] has degree [-1].

    How this answers [TBD1].  By bilinearity the 2-loop of
    [F(loop^i,loop^j)] is [ij] times that of [F(loop,loop)]; for [m_k]
    the latter is [kγ] (the [k]-loop around [id_S¹]).  Precomposing
    [m_1] with the degree [k] map in either argument multiplies the
    2-loop at [(loop,loop)] by [k] ([loops_reading_dg1],
    [loops_reading_dg2]), so under [M ≃ Ω²(B²ℤ) ≃ ℤ]
    (read off at [(loop,loop)]) [m_k = m_1 ∘ (dg_k × id) = m_1 ∘ (id ×
    dg_k)], and [m_k] corresponds to [k].

    The equivalence [M ≃ ℤ] (claimed in [exa:allS1*-swap]), with
    [B²ℤ :≡ Σ_{X:U} ‖S¹ = X‖₀] pointed at [(S¹,|refl|)] ([B2Z]) and
    [S¹ →* B²ℤ] pointed at the constant map ([pmap_ptd]):
    - [M_eqv_loops]: [M ≃ Ω(S¹ →* B²ℤ)] by evaluation at [loop]
      ([evp], [cor:circle-loopspace]; this is [ev] of
      [rem:pointing-ev]).
    - [loops_cst_eqv]: [Ω(S¹ →* B²ℤ) ≃ (S¹ →* ΩB²ℤ)], which is [ptw_*]
      ([con:identity-ptd-maps]) at the constant map, implemented
      directly ([lc_eqv], for any pointed [B]) so that a loop [ℓ] goes
      to [(apD10(ap_fst(ℓ)), e)] by definition.
    - [omega2_eqv]: [(S¹ →* ΩB²ℤ) ≃ Ω²B²ℤ], [evp] again.
    - [omega2_B2Z_eqv]: [Ω²B²ℤ ≃ ℤ], along the second argument of the
      example: the second component of [pt = pt] is a path in the set
      [‖S¹ = S¹‖₀], so [Ω²B²ℤ ≃ (refl_{S¹} = refl_{S¹})] ([sigma_step]);
      by univalence and function extensionality this is [∏_x (x = x)]
      ([ua_step]), which is [base = base] by evaluation at [base]
      ([ev_step], from [xca:(S1->S1)_(f)-eqv-S1]), and that is [ℤ] by
      [wdg].
    - [M_eqv_Z]: the composite [M ≃ ℤ].

    The direct equivalence [M_eqv_mult :
    M ≃ Σ_{h : S¹ × S¹ → S¹} (id_{S¹} = h(base,-))]:
    - [jmap : ΩB²ℤ → (S¹ → S¹)], [r ↦ ptoe(ap_fst(r))], is an embedding
      onto the component of [id]; [ap_jmap_eq]: on 2-loops [ap_j] is
      [ua0_step ∘ sigma_step], hence an equivalence ([ap_jmap_isEquiv]).
    - [post]: postcomposition with [j], [(S¹ →* ΩB²ℤ) → (S¹ →* (S¹ → S¹,
      id))] ([IdS1]); [evp_post]: [evp ∘ post = ap_j ∘ evp], so [post] is
      an equivalence ([post_eqv]; [S¹] being connected is what makes this
      work, via [evp]).
    - [uncurry_eqv], and [M_eqv_mult] as the composite with
      [M_eqv_loops] and [loops_cst_eqv].
    - [M_eqv_mult_m]: [m_k] goes to the uncurried [h_k], where
      [h_k(w,-)] goes around [id_S¹] along the [k]-loop
      [u ↦ ex(u)(loop^k)] as [w] goes around [loop] ([h_k :≡ S1_rec id
      (funext(kloop_pw k))]); [h_1] is the multiplication of [S¹].  The
      first variable of [h] is the inner variable [w] of [m] (the outer
      [z] is used up by evaluation at [loop]), the second is a point of
      [ΩB²ℤ ≃ S¹]; so the swap of [m] is not the swap of the variables of
      [h].
    - [M_eqv_mult_m_sigma]: with both components, [M_eqv_mult(m_k) =
      (h_k, refl)]; the pointing component is [refl] because the
      identification of the first components is [refl] at [base]
      ([S1_fun_path_base], [sigma_uncurry_path]).
    - [h_k_sigma] ([TBD1] in the Σ-type): [(h_k, refl) = (h_1 ∘ (dg_k × id),
      refl)], i.e. [h_k(w,u) = h_1(w^k,u)] ([h_dg], [h_k_dg]: on [loop],
      [ap_{h_1 ∘ dg_k}(loop) = (ap_{h_1}(loop))^k] is [funext] of the
      [k]-loop, [h_k_loop]; the base component is [refl], [h_k_dg_base]).

    The maps [m_k], for all [k : ℤ], as in the example:
    - [kloop k]: the [k]-loop around [id_S¹], pointwise
      [x ↦ ex(x)(loop^k)] ([kloop_pw]), made a 2-loop at [refl_{S¹}]
      by function extensionality and univalence ([kloop_id]) and then
      at [refl_{pt}] in [B²ℤ].
    - [dg_k' : S¹ →* ΩB²ℤ] with [dg_k'(base) :≡ refl], [dg_k'(loop) :=
      kloop k], pointed by [refl]; [m_k] with [m_k(base) :≡ pt],
      [m_k(loop) := ptw_*⁻¹(dg_k')] and [(m_k)_pt :≡ refl].
    - [M_eqv_Z_m]: [M_eqv_Z(m_k) = k].

    The w-outer reading of [m_k]:
    - [reading_lc] (any pointed [B]): for [m :≡ evp⁻¹(ℓ)] the w-outer
      reading of [F(z,w) :≡ m(z)(w)] at [(loop,loop)] is [evp] of
      [lc_eqv(ℓ)], with the sides identified with [refl] by [eP_of]
      (from the pointing path [e] of [lc_eqv(ℓ)]) and [eQ_of] ([ap] of
      a constant).  It rests on [reading_w_fun] (the reading in terms
      of [apD10] of [ap_G(p)]) and [const_reading] (for a constant
      function the reading of a homotopy [h] is [ap_h], conjugated).
    - [reading_m_k]: for [m_k] ([F_k], [eP_k], [eQ_k]) this is
      [kloop k]; [reading_m_k_Z]: it corresponds to [k] under
      [Ω²B²ℤ ≃ ℤ].
    - [Psi]: the composite [Ω²B²ℤ → (base = base)] as a single [ap]
      ([Psi_eq]), hence injective ([Psi_inj]) and preserving powers;
      [kloop_pow]: [kloop k = γ^k] with [γ :≡ kloop 1] ([gamma]).
    - [reading_m_1]: [γ] is the reading of [m_1];
      [reading_m_k_gamma]: the reading of [m_k] is [γ^k] ([loopexp]).
    - [reading_m_1_dg1], [reading_m_1_dg2] ([TBD1] for [k : ℕ]): the
      readings of [m_1 ∘ (dg_k × id)] and [m_1 ∘ (id × dg_k)] equal
      that of [m_k].


    Negative degrees and independence of the sides:
    - [loops_reading_indep]: the 2-loop of a square of loops does not
      depend on the identifications of its sides with [refl] (changing
      them conjugates it, and 2-loops commute: [eckmann_hilton]).
    - [loops_reading_inv1], [loops_reading_inv2]: [p⁻¹] gives the
      inverse 2-loop; [loops_reading_loopexp1], [loops_reading_loopexp2]:
      the integer power [p^z] ([loopexp], [z : Int]) gives [γ^z].
    - [dgZ k :≡ S1_rec base loop^k] for [k : ℤ] ([dg n ≡ dgZ(ι₊ n)],
      [dg_dgZ]); [loops_reading_dgZ1], [loops_reading_dgZ2]: precomposing
      with [dgZ k] in either argument gives [γ^k].
    - [reading_m_k_any]: the reading of [m_k] is [γ^k] for any side
      identifications; [reading_m_1_dgZ1], [reading_m_1_dgZ2] ([TBD1] for
      all [k : ℤ]): the readings of [m_1 ∘ (dg_k × id)] and
      [m_1 ∘ (id × dg_k)] equal that of [m_k].  The sign and the bilinearity are independent of all
    of this: they hold for any [F].

    [TBD2] in [M]: [swap(m_k) = m_{-k}] ([swap_m_k]):
    - [swapM]: the map [swap] of [con:swap-ptd-doms] for [M], defined
      directly, with [swap(m)(w) :≡ (z ↦ m(z)(w))] pointed by
      [ptw(fst(m_pt))(w)], and the outer pointing path with function part
      [funext(z ↦ m(z)_pt)]; no property claimed in that construction is
      used.  Its function of two variables is [swap2] of that of [m]
      ([swapM_fun], by definition).
    - [M_eqv_Z_swap]: [M_eqv_Z(swap(m_k)) = -k].  [M_eqv_Z] reads off the
      w-outer reading ([reading_lc]) after the identification
      [swap(m_k) = evp⁻¹(evp(swap(m_k)))] ([evp_inv_evp]); readings are
      transported along identifications of functions of two variables
      ([loops_reading_trp]), here along a loop at [pt] in [B²ℤ], which
      changes nothing since [B²ℤ] is simply connected
      ([B2Z_loop_merely_refl], [omega2_trp]); then the sign lemma
      [loops_reading_swap], [reading_m_k], and [kloop(-k) = (kloop k)⁻¹]
      ([kloop_neg], from [loopexp_neg]).
    - [swap_m_k]: since [M_eqv_Z] is an equivalence and
      [M_eqv_Z(m_{-k}) = -k] ([M_eqv_Z_m]). *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Cubical.DPath Truncations.Core
  Truncations.SeparatedTrunc Universes.TruncType Colimits.Quotient
  Spaces.Nat.Core Spaces.Nat.Factorial Spaces.Nat.Division
  Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Finite.Finite
  Spaces.List.Core Spaces.Int Spaces.Circle.
From SymmetryBook Require Export FinGroups.FinGroups.

Local Open Scope uf_scope.

(** ** 13.1 Rings, abstract and concrete *)

(** *** 13.1.1 Abstract rings *)

(** Definition [def:abstractring]: the distributive laws
    [DistrLaws(R,·,+)], parts [ring:ldistr-law] and [ring:rdistr-law]. *)
Definition DistrLaws (R : Type) (μ plus : R -> R -> R) : Type
  := (forall a b c : R, μ a (plus b c) = plus (μ a b) (μ a c))
     × (forall a b c : R, μ (plus a b) c = plus (μ a c) (μ b c)).

(** Definitions [def:abstractring] and [def:typering]: the type of
    abstract rings, as the book's iterated [Σ]-type (the book writes
    [Ring]; we write [AbsRing], keeping [Ring] for the concrete notion
    of [def:ring]). *)
Definition AbsRing : Type
  := {G : AbsGroup & {e : ag_S G & {μ : ag_S G -> ag_S G -> ag_S G &
       MonoidLaws (ag_S G) e μ × DistrLaws (ag_S G) μ (ag_mul G)}}}.

Section AbsRingData.

  Context (R : AbsRing).

  (** The (additive) group [(R,0,+,-)] and the (multiplicative) monoid
      [(R,1,·)] of [R]. *)
  Definition ar_grp : AbsGroup := fst R.
  Definition ar_S : Type := ag_S ar_grp.
  Definition ar_zero : ar_S := ag_e ar_grp.
  Definition ar_add : ar_S -> ar_S -> ar_S := ag_mul ar_grp.
  Definition ar_neg : ar_S -> ar_S := ag_inv ar_grp.
  Definition ar_one : ar_S := fst (snd R).
  Definition ar_mul : ar_S -> ar_S -> ar_S := fst (snd (snd R)).
  Definition ar_mlaws : MonoidLaws ar_S ar_one ar_mul := fst (snd (snd (snd R))).
  Definition ar_ldistr : forall a b c, ar_mul a (ar_add b c) = ar_add (ar_mul a b) (ar_mul a c)
    := fst (snd (snd (snd (snd R)))).
  Definition ar_rdistr : forall a b c, ar_mul (ar_add a b) c = ar_add (ar_mul a c) (ar_mul b c)
    := snd (snd (snd (snd (snd R)))).

  Definition ar_monoid : Monoid
    := {| mo_S := ar_S; mo_isSet := ag_isSet ar_grp; mo_e := ar_one; mo_mul := ar_mul;
          mo_runit := fun g => fst (fst (snd ar_mlaws) g);
          mo_lunit := fun g => snd (fst (snd ar_mlaws) g);
          mo_assoc := snd (snd ar_mlaws) |}.

  (** Non-trivial and commutative abstract rings. *)
  Definition ar_isNontrivial : Type := ar_zero ≠ ar_one.

  Definition ar_isComm : Type := forall a b : ar_S, ar_mul a b = ar_mul b a.

  (** Exercise [xca:ring-group-abelian], following the hint: expanding
      [(a+1)·(b+1)] with the left distributive law first gives
      [(a·b + b) + (a + 1)], with the right one first
      [(a·b + a) + (b + 1)]; cancel [a·b] and [1]. *)
  Definition xca_ring_group_abelian : ag_isAb ar_grp.
  Proof.
    intros a b.
    pose (one := ar_one). pose (mu := ar_mul).
    pose (l1 := fun g => snd (fst (snd ar_mlaws) g) : mu one g = g).
    pose (r1 := fun g => fst (fst (snd ar_mlaws) g) : mu g one = g).
    assert (E : ar_add (ar_add (mu a b) b) (ar_add a one)
                = ar_add (ar_add (mu a b) a) (ar_add b one)).
    { refine ((ap011 ar_add (ar_rdistr a one b @ ap (ar_add (mu a b)) (l1 b))
                 (r1 (ar_add a one)))^ @ _).
      refine ((ar_ldistr (ar_add a one) b one)^ @ _).
      refine (ar_rdistr a one (ar_add b one) @ _).
      exact (ap011 ar_add (ar_ldistr a b one @ ap (ar_add (mu a b)) (r1 a))
               (l1 (ar_add b one))). }
    pose (re := fun x y => ap (ar_add (mu a b)) (ag_assoc ar_grp x y one)^
                           @ ag_assoc ar_grp (mu a b) x (ar_add y one)).
    apply (ag_cancel_r ar_grp one).
    apply (ag_cancel_l ar_grp (mu a b)).
    exact (re a b @ E^ @ (re b a)^).
  Defined.

End AbsRingData.

(** The type of commutative abstract rings ([def:typering]). *)
Definition AbsCommRing : Type := {R : AbsRing & ar_isComm R}.

(** Definition [def:ringhom]: an abstract homomorphism of the additive
    groups that is a monoid homomorphism of the multiplicative monoids. *)
Definition AbsRingHom (R S : AbsRing) : Type
  := {f : absHom (ar_grp R) (ar_grp S) &
       (fst f (ar_one R) = ar_one S)
       × forall a b, fst f (ar_mul R a b) = ar_mul S (fst f a) (fst f b)}.

Definition AbsRingHom_monoid (R S : AbsRing) (f : AbsRingHom R S)
  : MonoidHom (ar_monoid R) (ar_monoid S)
  := (fst (fst f); snd f).

(** Example [exa:ring-Z-polynomials] is [TBD] in the book. *)

(** *** 13.1.2 Mixed rings *)

Section MixedRings.

  Context `{Funext}.

  (** Definition [def:mixring]: the laws [RingProps(R,1_R,ℓ,r)]
      ([mixring:unit-laws], [mixring:lr-coherence-law],
      [mixring:assoc-law]).  The associativity law [ℓ ∘ r = r ∘ ℓ] is
      read pointwise: [ℓ_g ∘ r_h = r_h ∘ ℓ_g] for all [g, h], expressing
      [g·(x·h) = (g·x)·h]. *)
  Definition RingProps (R : Group) (one : USym R) (l r : USym R -> Hom R R) : Type
    := ((l one = idG R) × (r one = idG R))
       × (forall g h : USym R, USymf (l g) h = USymf (r h) g)
       × (forall g h : USym R, compG (l g) (r h) = compG (r h) (l g)).

  (** Definition [def:typemixring]: the type of mixed rings. *)
  Definition MixRing : Type
    := {R : Group & {one : USym R & {l : USym R -> Hom R R & {r : USym R -> Hom R R &
         RingProps R one l r}}}}.

  Definition MixCommRing : Type
    := {R : Group & {one : USym R & {l : USym R -> Hom R R & {r : USym R -> Hom R R &
         RingProps R one l r × (l = r)}}}}.

  Definition mr_isNontrivial (R : MixRing) : Type := fst (snd R) ≠ refl.

  Section MixRingData.

    Context (R : MixRing).

    Local Notation G := (fst R).
    Local Notation one := (fst (snd R)).
    Local Notation l := (fst (snd (snd R))).
    Local Notation r := (fst (snd (snd (snd R)))).
    Definition mr_props : RingProps G one l r := snd (snd (snd (snd R))).

    (** [g·h :≡ (USym ℓ_g)(h)], which is [(USym r_h)(g)] by coherence. *)
    Definition mr_mul (g h : USym G) : USym G := USymf (l g) h.

    Definition USymf_idG (K : Group) (g : USym K) : USymf (idG K) g = g
      := trans_1p _ @ ap_idmap g.

    (** Exercise [xca:Rmixring->URabstring]: [USym R] is an abstract ring
        with additive group [abstr(R)] and multiplicative monoid
        [(USym R, 1_R, ·)]. *)
    Definition mr_mlaws : MonoidLaws (USym G) one mr_mul.
    Proof.
      refine (USym_isSet G; ((fun g => (_; _)); _)).
      - refine (snd (fst mr_props) g one @ _).
        refine (ap (fun f => USymf f g) (snd (fst (fst mr_props))) @ _).
        exact (USymf_idG G g).
      - refine (ap (fun f => USymf f g) (fst (fst (fst mr_props))) @ _).
        exact (USymf_idG G g).
      - intros g1 g2 g3. unfold mr_mul.
        refine (ap (USymf (l g1)) (snd (fst mr_props) g2 g3) @ _).
        refine ((ap10 (USym_compose (r g3) (l g1)) g2)^ @ _).
        refine (ap (fun f => USymf f g2) (snd mr_props g1 g3) @ _).
        refine (ap10 (USym_compose (l g1) (r g3)) g2 @ _).
        exact (snd (fst mr_props) _ g3)^.
    Defined.

    Definition mr_distr : DistrLaws (USym G) mr_mul (ag_mul (abstr G)).
    Proof.
      split.
      - intros a b c. exact (USymf_comp (l a) c b).
      - intros a b c. unfold mr_mul.
        refine (snd (fst mr_props) _ c @ _).
        refine (USymf_comp (r c) b a @ _).
        exact (ap011 (fun x y => x ⋅ y) (snd (fst mr_props) a c)^ (snd (fst mr_props) b c)^).
    Defined.

    Definition xca_Rmixring_URabstring : AbsRing
      := (abstr G; (one; (mr_mul; (mr_mlaws; mr_distr)))).

    (** As in [xca:ring-group-abelian], the group [R] is abelian. *)
    Definition mr_grp_abelian : ag_isAb (abstr G)
      := xca_ring_group_abelian xca_Rmixring_URabstring.

  End MixRingData.

End MixedRings.

(** The example after [def:mixring]: the integers as a mixed ring, with
    [1_ℤ :≡ loop] and [ℓ_g = r_g] classified by [Bℓ_g(base) :≡ base],
    [Bℓ_g(loop) := g], pointed by [refl] ([veG] of Section 4.4). *)
Section IntMixRing.

  Context `{Univalence}.

  Definition Z_ell (g : USym ZZ) : Hom ZZ ZZ := veG ZZ g.

  Definition Hom_ZZ_path {K : Group} (f f' : Hom ZZ K)
    (e : fst (Hom_ZZ_eqv K) f = fst (Hom_ZZ_eqv K) f') : f = f'
    := (eqinv_l (snd (Hom_ZZ_eqv K)) f)^ @ ap (eqinv (snd (Hom_ZZ_eqv K))) e
       @ eqinv_l (snd (Hom_ZZ_eqv K)) f'.

  Definition Z_ell_loop (g : USym ZZ) : fst (Hom_ZZ_eqv ZZ) (Z_ell g) = g
    := trans_1p _ @ S1_rec_loop _ _ _.

  (** [ap_{Bℓ_g}(loop^n) = g^n]. *)
  Definition Z_ell_ap (g : USym ZZ) (n : Int)
    : USymf (Z_ell g) (loopexp loop n) = loopexp g n
    := trans_1p _ @ ap_loopexp _ loop n @ ap (fun s => loopexp s n) (S1_rec_loop _ _ _).

  Definition Z_coh (g h : USym ZZ) : USymf (Z_ell g) h = USymf (Z_ell h) g.
  Proof.
    rewrite <- (loopZ_wdg g), <- (loopZ_wdg h). unfold loopZ.
    refine (Z_ell_ap _ _ @ loopexp_mul loop _ _ @ _).
    refine (ap (loopexp loop) (int_mul_comm _ _) @ _).
    exact (Z_ell_ap _ _ @ loopexp_mul loop _ _)^.
  Defined.

  Definition Z_props : RingProps ZZ loop Z_ell Z_ell.
  Proof.
    pose (u := Hom_ZZ_path (Z_ell loop) (idG ZZ)
                 (Z_ell_loop loop @ (trans_1p _ @ ap_idmap loop)^)).
    refine (((u; u); Z_coh); _).
    intros g h. apply Hom_ZZ_path.
    refine (Znatural _ _ _ _ @ _ @ (Znatural _ _ _ _)^).
    refine (ap (USymf (Z_ell g)) (Z_ell_loop h) @ _).
    exact (Z_coh g h @ ap (USymf (Z_ell h)) (Z_ell_loop g)^).
  Defined.

  Definition Z_mixring : MixRing := (ZZ; (loop; (Z_ell; (Z_ell; Z_props)))).

  Definition Z_mixcommring : MixCommRing
    := (ZZ; (loop; (Z_ell; (Z_ell; (Z_props; refl))))).

  Definition Z_mixring_nontrivial : mr_isNontrivial Z_mixring := loop_ne_refl.

End IntMixRing.


(** *** Subsection "Move to a better place (Ch. 11 or 2)": pointed
    homotopies, [Ω] and [O] *)

(** [X →* Y] pointed at the constant map [(cst_{pt}, refl)]. *)
Definition pmap_ptd (X Y : Ustar) : Ustar
  := ((X →* Y); ((fun _ => pt Y); refl)).

Section PtdHomotopies.

  Context `{Funext} {X Y : Ustar}.

  (** The type [H(f,g)] of [con:identity-ptd-maps]. *)
  Definition Hpt (f g : X →* Y) : Type
    := {h : forall x, fst f x = fst g x & h (pt X) ⋅ snd f = snd g}.

  (** [ptw_*], as in exercise [xca:identity-ptd-maps], by induction
      ([ptw_star_ind]).  It is an equivalence: on total spaces it is a
      map between contractible types, [Σ_g H(f,g)] being contractible
      since [ptw_star] (the book's chain of equivalences) is a fiberwise
      equivalence.  We use this version since it computes on [refl]. *)
  Definition Hpt_tot_isContr (f : X →* Y) : isContr {g : X →* Y & Hpt f g}
    := isContr_Eqv (tot (fun g => fst (ptw_star f g)); tot_isEquiv _ (fun g => snd (ptw_star f g)))
         (singleton_contr f).

  Definition ptw_star_ind_isEquiv (f g : X →* Y) : isEquiv (@ptw_star_ind X Y f g)
    := isEquiv_from_tot (fun g => @ptw_star_ind X Y f g)
         (contr_map_isEquiv (singleton_contr f) (Hpt_tot_isContr f) _) g.

  Definition ptw_ind_eqv (f g : X →* Y) : (f = g) ≃ Hpt f g
    := (ptw_star_ind; ptw_star_ind_isEquiv f g).

  (** Identifying pointed maps by a pointed homotopy. *)
  Definition pmap_path {f g : X →* Y} (h : forall x, fst f x = fst g x)
    (c : h (pt X) ⋅ snd f = snd g) : f = g
    := eqinv (snd (ptw_ind_eqv f g)) (h; c).

  (** Definition [def:ptd-homotopy-compo]: pointwise composition
      [k' ·_ptw k :≡ (x ↦ k'(x) · k(x), k'_pt · ap_{k'(pt) · -}(k_pt))]
      (with the associativity of path composition made explicit). *)
  Definition ptw_comp {f g h : X →* Y} (k : Hpt f g) (k' : Hpt g h) : Hpt f h
    := ((fun x => fst k' x ⋅ fst k x);
        snd k' ⋅ (ap (fun u => fst k' (pt X) ⋅ u) (snd k)
                  ⋅ (trans_assoc (snd f) (fst k (pt X)) (fst k' (pt X)))⁻¹)).

  (** Construction [con:ptd-homotopy-compo]: [ptw_*(qp) = ptw_*(q) ·_ptw
      ptw_*(p)], by induction on [q] and [p]. *)
  Definition con_ptd_homotopy_compo {f g h : X →* Y} (p : f = g) (q : g = h)
    : ptw_star_ind (q ⋅ p) = ptw_comp (ptw_star_ind p) (ptw_star_ind q).
  Proof. destruct q, p. exact refl. Defined.

End PtdHomotopies.

(** Definition [def:cst-ptd]: the pointed constant map [cst_*^A(b,p) :≡
    (cst_b, p)]. *)
Definition cst_ptd (A : Ustar) {B : Ustar} (w : {x : utype B & pt B = x}) : A →* B
  := ((fun _ => fst w); snd w).

(** The path [(p, ρ_p) : (b, refl) = (b', p)] in [Σ_x (pt_B = x)], by
    induction on [p]. *)
Definition cst_path {B : Type} {b b' : B} (p : b = b')
  : ((b; refl) : {x : B & b = x}) = (b'; p)
  := match p with refl => refl end.

(** Remark [rem:loops-at-ptd-cst]: the variant [ptw_* : Ω(X →* Y) ≃
    (X →* ΩY)], replacing [h(pt_X) · refl = refl] by [refl = h(pt_X)]
    (laws of symmetry and right unit). *)
Definition ptwc `{Funext} (X Y : Ustar)
  : (pt (pmap_ptd X Y) = pt (pmap_ptd X Y)) ≃ (X →* loops Y).
Proof.
  refine (Eqv_comp (ptw_ind_eqv _ _) _).
  exact (tot (fun h => fst (Eqv_comp (eq_l_eqv (trans_1p (h (pt X)))) symm_eqv));
         tot_isEquiv _ (fun h => snd (Eqv_comp (eq_l_eqv (trans_1p (h (pt X)))) symm_eqv))).
Defined.

(** Construction [con:Id-(B->*A)]: given a section [s] of
    [ev : (id_A = id_A) → (pt_A = pt_A)], an identification of the
    underlying maps of [f, f' : B →* A] gives one of [f] and [f'];
    by induction on [f_÷ = f'_÷] and on [f_pt], with
    [h(b) :≡ ptw(s(r))(f(b))] for [r :≡ f'_pt · f_pt⁻¹]. *)
Definition con_Id_ptd `{Funext} (A : Ustar)
  (s : (pt A = pt A) -> (id (utype A) = id (utype A)))
  (sec : forall p, ptw (s p) (pt A) = p)
  (B : Ustar) (f f' : B →* A) (e : fst f = fst f') : f = f'.
Proof.
  destruct A as [A a], f as [f fp], f' as [f' fp']. cbn in *. destruct e.
  revert s sec fp'. revert a fp. refine (paths_ind_r _ _ _). intros s sec fp'.
  refine (@pmap_path _ B (_; _) ((f; refl) : B →* (A; _)) ((f; fp') : B →* (A; _))
            (fun b => ptw (s (fp' ⋅ refl⁻¹)) (f b)) _).
  exact (trans_1p _ @ sec _ @ trans_1p fp').
Defined.

(** Exercise [xca:ev-section-loopsA]: [ρ_q : q · refl = q] and
    [i(β) : ap_{- · refl}(β) = β · ρ_p], by induction; hence
    [ap_{- · refl}(α) = α] for [α : refl = refl]. *)
Section EvSection.

  Context {A : Type} {a : A}.

  Definition rho_r {x : A} (q : a = x) : q ⋅ refl = q := trans_1p q.

  Definition i_beta {p : a = a} (β : p = refl)
    : ap (fun x => x ⋅ refl) β = β ⋅ rho_r p.
  Proof. revert p β. refine (paths_ind_r _ _ _). exact refl. Defined.

  Definition xca_ev_section_loopsA (α : refl a = refl a)
    : ap (fun x => x ⋅ refl) α = α
    := i_beta α @ trans_1p α.

End EvSection.

(** Construction [con:ev-section-loopsA]: [ev : (id_{ΩA} = id_{ΩA}) →
    (rfl = rfl)], [i ↦ ptw(i)(rfl)], has the section
    [α ↦ ptw⁻¹(p ↦ ap_{- · p}(α))]. *)
Section EvSectionLoops.

  Context `{Funext} (A : Ustar).

  Definition ev_loops (i : id (pt A = pt A) = id (pt A = pt A)) : refl (pt A) = refl (pt A)
    := ptw i refl.

  Definition s_loops (α : refl (pt A) = refl (pt A)) : id (pt A = pt A) = id (pt A = pt A)
    := ptw_inv (fun p => ap (fun x => x ⋅ p) α).

  Definition con_ev_section_loopsA (α : refl (pt A) = refl (pt A))
    : ev_loops (s_loops α) = α
    := ptw (eqinv_r (funext (id _) (id _)) (fun p => ap (fun x => x ⋅ p) α)) refl
       @ xca_ev_section_loopsA α.

End EvSectionLoops.

(** Corollary [cor:Id-(B->*loopsA)]. *)
Definition cor_Id_ptd_loops `{Funext} (A B : Ustar) (f f' : B →* loops A)
  (e : fst f = fst f') : f = f'
  := con_Id_ptd (loops A) (s_loops A) (con_ev_section_loopsA A) B f f' e.

(** Definition [def:O-functor]: [O A :≡ (S¹ →* A)], and [O(f)] is
    composition with [f], pointed by [ap_{cst_*}(f_pt, ρ_{f_pt})]
    ([cst_path]); [O(f)_pt ≡ refl] when [f_pt ≡ refl]. *)
Definition OO (A : Ustar) : Ustar := pmap_ptd S1star A.

Definition OO_pt {A B : Ustar} (f : A →* B)
  : pt (OO B) = pcomp f (pt (OO A))
  := ap (cst_ptd S1star) (cst_path (snd f)).

Definition OO_f {A B : Ustar} (f : A →* B) : OO A →* OO B
  := ((fun g => pcomp f g); OO_pt f).

(** Exercise [xca:O-functor]: [O] preserves identities and composition,
    and [O(f)_pt = ptw_*⁻¹(cst_{f_pt}, ρ_{f_pt})]. *)
Section OFunctor.

  Context `{Funext}.

  Definition OO_pid (A : Ustar) : OO_f (pid A) = pid (OO A)
    := @pmap_path _ (OO A) (OO A) (OO_f (pid A)) (pid (OO A))
         (fun g : S1star →* A => pcomp_pid_l g) refl.

  Definition OO_pcomp {A B C : Ustar} (g : B →* C) (f : A →* B)
    : OO_f (pcomp g f) = pcomp (OO_f g) (OO_f f).
  Proof.
    refine (@pmap_path _ (OO A) (OO C) (OO_f (pcomp g f)) (pcomp (OO_f g) (OO_f f))
              (fun h : S1star →* A => (pcomp_assoc g f h)^) _).
    destruct g as [g gp], f as [f fp].
    destruct A as [A a], B as [B b], C as [C c]. cbn in *.
    revert c gp. refine (paths_ind_r _ _ _).
    revert b fp. refine (paths_ind_r _ _ _).
    exact refl.
  Defined.

  Definition OO_pt_ptw {A B : Ustar} (f : A →* B)
    : OO_pt f = eqinv (snd (ptw_ind_eqv (pt (OO B)) (pcomp f (pt (OO A)))))
                  ((fun _ => snd f); rho_r (snd f)).
  Proof.
    refine ((eqinv_l (snd (ptw_ind_eqv _ _)) (OO_pt f))^ @ _).
    apply (ap (eqinv (snd (ptw_ind_eqv _ _)))).
    destruct A as [A a], B as [B b], f as [f fp]. cbn in *.
    revert b fp. refine (paths_ind_r _ _ _). exact refl.
  Defined.

End OFunctor.

(** Remark [rem:pointing-ev]: [ev_A : (S¹ →* A) → ΩA] is pointed by
    [ε_A(loop)], with [ε_A(p) : refl = cst_{pt}(p) · refl] defined by
    induction on [p] (here with [evp]'s form of [Ω(f)(loop)]). *)
Definition eps_ev (A : Ustar) {z : S1} (p : base = z)
  : refl (pt A) = (refl (pt A))⁻¹ ⋅ (ap (fun _ : S1 => pt A) p ⋅ refl)
  := match p with refl => refl end.

Definition evpt (A : Ustar) : OO A →* loops A
  := (evp (pt A); eps_ev A loop).

(** Exercise [xca:allptd-S1-contractible]. *)
Definition pmap_conn_set_isContr `{Funext} {X S : Ustar} (cX : isConn (utype X))
  (sS : isSet (utype S)) : isContr (X →* S).
Proof.
  refine (((fun _ => pt S); refl); _). intro f.
  refine (@pmap_path _ X S (((fun _ => pt S); refl) : X →* S) f (fun x => ptrunc_rec (sS _ _) (fun p => ap (fst f) p ⋅ snd f)
                                (snd cX (pt X) x)) _).
  exact (sS _ _ _ _).
Defined.

Definition xca_allptd_S1_contractible `{Funext} (X Y Z : Ustar)
  (cX : isConn (utype X)) (cY : isConn (utype Y)) (gZ : isGrpd (utype Z))
  : isContr (X →* pmap_ptd Y Z)
  := @pmap_conn_set_isContr _ X (pmap_ptd Y Z) cX (pmap_isSet (X := Y) (Y := Z) cY gZ).

(** Construction [con:swap-on-paths]: for [g(b)(a) :≡ f(a)(b)] and
    [q : b = b'], [f(-)(q) = ptw(g(q))], by induction on [q]. *)
Definition con_swap_on_paths {A B C : Type} (f : A -> B -> C) {b b' : B} (q : b = b')
  : (fun a => ap (f a) q) = ptw (ap (fun b a => f a b) q).
Proof. destruct q. exact refl. Defined.

(** [ι(f,p,g)], by induction on [g]. *)
Definition iota {A B : Type} (f : A -> B) (p : S1 -> A) {z : S1} (g : base = z)
  : ap f (ap p g ⋅ refl) ⋅ refl = ap (fun x => f (p x)) g ⋅ refl
  := match g with refl => refl end.

Definition iota_gen {A B : Type} (f : A -> B) (a : A) (p : S1 -> A) (pp : a = p base)
  : loops_fun (((f; refl) : (A; a) →* (B; f a))) (evp a (p; pp))
    = evp (f a) (pcomp ((f; refl) : (A; a) →* (B; f a)) ((p; pp) : S1star →* (A; a))).
Proof. revert a pp. refine (paths_ind_r _ _ _). exact (iota f p loop). Defined.

Definition iota_coh {A B : Type} (f : A -> B) (a : A) {z : S1} (g : base = z)
  : iota f (fun _ : S1 => a) g
    ⋅ (ap (loops_fun (((f; refl) : (A; a) →* (B; f a)))) (eps_ev (A; a) g) ⋅ refl)
    = eps_ev (B; f a) g
  := match g with refl => refl end.

(** Construction [con:Omega-O]: [Ω(f) ∘ ev_A = ev_B ∘ O(f)] as pointed
    maps.  The underlying maps are identified at [(p, p_pt)] by
    [i(f,f_pt)(p,p_pt)], by induction on [p_pt] and [f_pt], reducing to
    [ι(f,p,loop)]; the triangle for the pointing paths becomes, after
    generalizing [loop] to [g : base = z], a reflexivity triangle at
    [g ≡ refl] ([iota_coh]). *)
Definition con_Omega_O `{Funext} {A B : Ustar} (f : A →* B)
  : pcomp (loops_map f) (evpt A) = pcomp (evpt B) (OO_f f).
Proof.
  destruct f as [f fp], A as [A a], B as [B b]. cbn in *.
  revert b fp. refine (paths_ind_r _ _ _).
  refine (@pmap_path _ (OO (A; a)) (loops (B; f a))
            (pcomp (loops_map ((f; refl) : (A; a) →* (B; f a))) (evpt (A; a)))
            (pcomp (evpt (B; f a)) (OO_f ((f; refl) : (A; a) →* (B; f a))))
            (fun p => iota_gen f a (fst p) (snd p)) _).
  exact (iota_coh f a loop).
Defined.

(** The second part of [con:Omega-O]: the equivalence [e :≡ ev_B⁻¹ ∘ (- ∘
    ev_A) : (ΩA →* ΩB) ≃ (OA →* OB)] and [O = e ∘ Ω].  We obtain [e] by
    transport along the paths [OA = ΩA] given by the pointed
    equivalences [ev] (univalence, [path_to_pEqv_isEquiv]), so that it is
    an equivalence by construction; it is characterized by
    [ev_B ∘ e(φ) = φ ∘ ev_A] ([e_OmegaO_char]), and [O = e ∘ Ω]
    ([OO_e_loops]) follows from the first part. *)
Section EqvOmegaO.

  Context `{Univalence}.

  Definition pmap_tr {X X' Y Y' : Ustar} (p : X = X') (q : Y = Y') (φ : X →* Y) : X' →* Y'
    := match p, q with refl, refl => φ end.

  Definition pmap_tr_isEquiv {X X' Y Y' : Ustar} (p : X = X') (q : Y = Y')
    : isEquiv (pmap_tr p q).
  Proof.
    refine (iso_to_isEquiv _ (pmap_tr p^ q^) _ _); intro φ; destruct p, q; exact refl.
  Defined.

  Local Notation pE p := (fst (path_to_pEqv p)).

  Definition pmap_tr_char {X X' Y Y' : Ustar} (p : X = X') (q : Y = Y') (φ : X →* Y)
    : pcomp (pE q) φ = pcomp (pmap_tr p q φ) (pE p).
  Proof. destruct p, q. exact (pcomp_pid_l φ). Defined.

  Definition pmap_tr_from {X X' Y Y' : Ustar} (p : X = X') (q : Y = Y') (φ : X →* Y)
    (ψ : X' →* Y') (r : pcomp (pE q) φ = pcomp ψ (pE p)) : pmap_tr p q φ = ψ.
  Proof. destruct p, q. exact ((pcomp_pid_l φ)^ @ r). Defined.

  (** [ev_A] as a pointed equivalence, and the corresponding path. *)
  Definition evpEqv (A : Ustar) : OO A ≃* loops A := (evpt A; evp_isEquiv (pt A)).

  Definition evPath (A : Ustar) : OO A = loops A
    := eqinv (path_to_pEqv_isEquiv (OO A) (loops A)) (evpEqv A).

  Definition evPath_pE (A : Ustar) : pE (evPath A) = evpt A
    := ap fst (eqinv_r (path_to_pEqv_isEquiv (OO A) (loops A)) (evpEqv A)).

  (** The equivalence [e : (ΩA →* ΩB) ≃ (OA →* OB)], characterized by
      [ev_B ∘ e(φ) = φ ∘ ev_A], that is, [e(φ) = ev_B⁻¹ ∘ φ ∘ ev_A]. *)
  Definition e_OmegaO (A B : Ustar) : (loops A →* loops B) ≃ (OO A →* OO B)
    := Eqv_inv (pmap_tr (evPath A) (evPath B); pmap_tr_isEquiv _ _).

  Definition e_OmegaO_char (A B : Ustar) (φ : loops A →* loops B)
    : pcomp (evpt B) (fst (e_OmegaO A B) φ) = pcomp φ (evpt A).
  Proof.
    refine (ap (fun k => pcomp k _) (evPath_pE B)^ @ _).
    refine (pmap_tr_char (evPath A) (evPath B) _ @ _).
    refine (ap (fun k => pcomp k _)
              (eqinv_r (pmap_tr_isEquiv (evPath A) (evPath B)) φ) @ _).
    exact (ap (pcomp φ) (evPath_pE A)).
  Defined.

  (** [O = e ∘ Ω]. *)
  Definition OO_e_loops (A B : Ustar)
    : (fun f : A →* B => OO_f f) = (fun f => fst (e_OmegaO A B) (loops_map f)).
  Proof.
    apply path_forall. intro f.
    refine ((eqinv_l (pmap_tr_isEquiv (evPath A) (evPath B)) (OO_f f))^ @ _).
    apply (ap (eqinv (pmap_tr_isEquiv (evPath A) (evPath B)))).
    apply pmap_tr_from.
    refine (ap (fun k => pcomp k _) (evPath_pE B) @ _).
    refine ((con_Omega_O f)^ @ _).
    exact (ap (pcomp _) (evPath_pE A))^.
  Defined.

End EqvOmegaO.

(** Construction [con:swap-ptd-doms] (its implementation is [TBD] in the
    book; we follow the book's hint).  [X →* (Y →* Z)] is equivalent to
    the type [SwapData X Y] of totally unpointed maps [F : X → Y → Z]
    with pointings [e2(x) : pt_Z = F(x,pt_Y)] (from the values) and
    [e1(y) : pt_Z = F(pt_X,y)] (from [f_pt], via [ptw_*]) and the
    coherence [e1(pt_Y) = e2(pt_X)] ([sd_fw], [sd_bw], [sd_retr],
    [sd_sec]).  Swapping the arguments and the two pointings, and
    inverting the coherence, is an involution of these data
    ([sd_sigma]); [swap] is the composite, an equivalence since it is
    an involution ([swap_swap], [swap_isEquiv]), pointed by
    [swap_ptd_pt], and [swap_÷÷] is the swap of the arguments by
    definition ([swap_divdiv]). *)
Section SwapPtdDoms.

  Context `{Funext} (Z : Ustar).

  (** Totally unpointed maps with the additional structure: both
      pointings and their coherence at [(pt_X, pt_Y)]. *)
  Definition SwapData (X Y : Ustar) : Type
    := {F : utype X -> utype Y -> utype Z &
        {e2 : forall x, pt Z = F x (pt Y) &
        {e1 : forall y, pt Z = F (pt X) y & e1 (pt Y) = e2 (pt X)}}}.

  Definition sd_fw {X Y : Ustar} (f : X →* pmap_ptd Y Z) : SwapData X Y
    := ((fun x y => fst (fst f x) y);
        ((fun x => snd (fst f x));
         (fst (ptw_star_ind (snd f)); (trans_1p _)^ @ snd (ptw_star_ind (snd f))))).

  Definition sd_bw {X Y : Ustar} (d : SwapData X Y) : X →* pmap_ptd Y Z
    := ((fun x => ((fst d x; fst (snd d) x) : Y →* Z));
        eqinv (snd (ptw_ind_eqv (pt (pmap_ptd Y Z)) ((fst d (pt X); fst (snd d) (pt X)) : Y →* Z)))
          (fst (snd (snd d)); trans_1p _ @ snd (snd (snd d)))).

  Definition sd_retr {X Y : Ustar} (f : X →* pmap_ptd Y Z) : sd_bw (sd_fw f) = f.
  Proof.
    destruct f as [g gp]. unfold sd_fw, sd_bw.
    apply (ap (fun q => ((g; q) : X →* pmap_ptd Y Z))).
    refine (_ @ eqinv_l (snd (ptw_ind_eqv _ _)) gp).
    apply (ap (eqinv (snd (ptw_ind_eqv _ _)))).
    refine (ap (fun c => (fst (ptw_star_ind gp); c)) _).
    exact (concat_p_Vp _ _).
  Defined.

  Definition sd_sec {X Y : Ustar} (d : SwapData X Y) : sd_fw (sd_bw d) = d.
  Proof.
    destruct d as [F [e2 [e1 c]]].
    pose (E := ptw_ind_eqv (pt (pmap_ptd Y Z)) ((F (pt X); e2 (pt X)) : Y →* Z)).
    pose (v := (e1; trans_1p _ @ c) : Hpt (pt (pmap_ptd Y Z)) ((F (pt X); e2 (pt X)) : Y →* Z)).
    pose (r := eqinv_r (snd E) v).
    change ((((fun x y => F x y); (e2; (fst (ptw_star_ind (eqinv (snd E) v));
              (trans_1p _)^ @ snd (ptw_star_ind (eqinv (snd E) v))))) : SwapData X Y)
            = (F; (e2; (e1; c)))).
    clearbody r. revert r. generalize (eqinv (snd E) v). intros w r.
    change (ptw_star_ind w = v) in r.
    refine (ap (fun k : Hpt (pt (pmap_ptd Y Z)) ((F (pt X); e2 (pt X)) : Y →* Z)
                => (((fun x y => F x y); (e2; (fst k; (trans_1p (fst k (pt Y)))^ @ snd k)))
                    : SwapData X Y)) r @ _).
    exact (ap (fun c' => (F; (e2; (e1; c'))) : SwapData X Y) (concat_V_pp _ _)).
  Defined.

  Definition sd_sigma {X Y : Ustar} (d : SwapData X Y) : SwapData Y X
    := ((fun y x => fst d x y); (fst (snd (snd d)); (fst (snd d); (snd (snd (snd d)))^))).

  Definition sd_sigma_sigma {X Y : Ustar} (d : SwapData X Y) : sd_sigma (sd_sigma d) = d
    := ap (fun c => (fst d; (fst (snd d); (fst (snd (snd d)); c)))) (inv_V _).

  (** Construction [con:swap-ptd-doms]. *)
  Definition swap_fun (X Y : Ustar) (f : X →* pmap_ptd Y Z) : Y →* pmap_ptd X Z
    := sd_bw (sd_sigma (sd_fw f)).

  Definition swap_swap (X Y : Ustar) (f : X →* pmap_ptd Y Z) : swap_fun Y X (swap_fun X Y f) = f
    := ap (fun d => sd_bw (sd_sigma d)) (sd_sec _) @ ap sd_bw (sd_sigma_sigma _) @ sd_retr f.

  Definition swap_isEquiv (X Y : Ustar) : isEquiv (swap_fun X Y)
    := iso_to_isEquiv _ (swap_fun Y X) (swap_swap X Y) (swap_swap Y X).

  Definition swap_ptd_pt (X Y : Ustar)
    : pt (pmap_ptd Y (pmap_ptd X Z)) = swap_fun X Y (pt (pmap_ptd X (pmap_ptd Y Z)))
    := ap (fun q => (((fun y => pt (pmap_ptd X Z)) : utype Y -> (X →* Z)); q)
                      : Y →* pmap_ptd X Z)
          (eqinv_l (snd (ptw_ind_eqv (pt (pmap_ptd X Z)) (pt (pmap_ptd X Z)))) refl)^.

  (** [swap_÷÷] is the swapping of arguments, by definition. *)
  Definition swap_divdiv (X Y : Ustar) (f : X →* pmap_ptd Y Z)
    : (fun y x => fst (fst (swap_fun X Y f) y) x) = (fun y x => fst (fst f x) y)
    := refl.

End SwapPtdDoms.

(** The first component of [ptw_*] is [ap] of evaluation. *)
Definition pw_ap {X Y : Ustar} {f g : X →* Y} (e : f = g) (x : utype X)
  : fst (ptw_star_ind e) x = ap (fun k : X →* Y => fst k x) e
  := match e with refl => refl end.

Definition conj_ap {P Q : Type} (h : P -> Q) {a b : P} (s : a = b) (l : b = b)
  : ap h (s⁻¹ ⋅ (l ⋅ s)) = (ap h s)⁻¹ ⋅ (ap h l ⋅ ap h s).
Proof. revert l. destruct s. intro l. exact (ap (ap h) (trans_1p l) @ (trans_1p (ap h l))^). Defined.

(** Construction [con:ptw-swap-ptd-doms]: [ev ∘ swap(-) = ptw_* ∘ ev] on
    [S¹ →* (X →* Y)]; by [cor:Id-(B->*loopsA)] only the underlying maps
    need to be identified, and at [x] both are the conjugate of
    [ap_{z ↦ f(z)(x)}(loop)] by [f'_pt(x)]. *)
Definition con_ptw_swap_ptd_doms `{Funext} (X Y : Ustar)
  : (fun f : S1star →* pmap_ptd X Y => pcomp (evpt Y) (swap_fun Y S1star X f))
    = (fun f => fst (ptwc X Y) (evp _ f)).
Proof.
  apply path_forall. intro f.
  apply (cor_Id_ptd_loops Y X).
  apply path_forall. intro x.
  pose (evx := fun k : X →* Y => fst k x).
  refine (_ @ (pw_ap (evp _ f) x)^).
  refine (_ @ (conj_ap evx (snd f) (ap (fst f) loop))^).
  refine (_ @ ap (fun u => (ap evx (snd f))⁻¹ ⋅ (u ⋅ ap evx (snd f)))
              (ap_compose (fst f) evx loop)).
  exact (ap (fun e => e⁻¹ ⋅ (ap (fun z => fst (fst f z) x) loop ⋅ e)) (pw_ap (snd f) x)).
Defined.

(** *** Example [exa:allS1*-swap], [TBD1] and [TBD2]: bilinearity and
    the sign of [swap] *)

(** A path over [p] in the family [x ↦ (u(x) = v(x))] is a square with
    sides [ap_u(p)] and [ap_v(p)]; defined by induction on [p]. *)
Definition po_sq {X Y : Type} {u v : X -> Y} {x x' : X} (p : x = x')
  {α : u x = v x} {β : u x' = v x'}
  : PathOver (fun x => u x = v x) p α β -> (ap v p ⋅ α = β ⋅ ap u p).
Proof.
  destruct p. intro r. exact ((trans_1p β)⁻¹ ⋅ r).
Defined.

Section SquareReadings.

  Context {A B C : Type} (F : A -> B -> C).

  (** The z-outer reading of the square [F(p,q)]. *)
  Definition reading_z {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : ap (fun z => F z b') p ⋅ ap (F a) q = ap (F a') q ⋅ ap (fun z => F z b) p
    := po_sq (u := fun z => F z b) (v := fun z => F z b') p
             (apd (fun z => ap (F z) q) p).

  (** The w-outer reading of the square [F(p,q)]. *)
  Definition reading_w {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : ap (F a') q ⋅ ap (fun z => F z b) p = ap (fun z => F z b') p ⋅ ap (F a) q
    := po_sq (u := F a) (v := F a') q
             (apd (fun w => ap (fun z => F z w) p) q).

  (** The sign: the two readings are inverse to each other. *)
  Definition reading_w_z {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : reading_w p q = (reading_z p q)⁻¹.
  Proof. destruct p, q. exact refl. Defined.

End SquareReadings.

(** Swapping the arguments of a function of two variables. *)
Definition swap2 {A B C : Type} (F : A -> B -> C) : B -> A -> C
  := fun w z => F z w.

(** The w-outer reading of [swap2 F] is the z-outer reading of [F]. *)
Definition reading_w_swap_jdeq {A B C : Type} (F : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : reading_w (swap2 F) q p = reading_z F p q
  := refl.

Definition reading_w_swap {A B C : Type} (F : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : reading_w (swap2 F) q p = (reading_w F p q)⁻¹
  := (symm_symm (reading_z F p q) ⋅ ap symm (reading_w_z F p q))⁻¹.

(** *** Squares and their pasting

    A square with top [t], bottom [bo], left [l] and right [r] is an
    identification [r ⋅ t = bo ⋅ l]; [reading_w F p q] is a square with
    [t :≡ ap_{F(-,b)}(p)], [bo :≡ ap_{F(-,b')}(p)], [l :≡ ap_{F(a,-)}(q)]
    and [r :≡ ap_{F(a',-)}(q)]. *)
Section Squares.

  Context {C : Type}.

  Definition Sq {c00 c10 c01 c11 : C} (t : c00 = c10) (bo : c01 = c11)
    (l : c00 = c01) (r : c10 = c11) : Type
    := r ⋅ t = bo ⋅ l.

  (** Horizontal pasting. *)
  Definition hpaste {c00 c10 c20 c01 c11 c21 : C}
    {t1 : c00 = c10} {b1 : c01 = c11} {l : c00 = c01} {m : c10 = c11}
    {t2 : c10 = c20} {b2 : c11 = c21} {r : c20 = c21}
    (s1 : Sq t1 b1 l m) (s2 : Sq t2 b2 m r) : Sq (t2 ⋅ t1) (b2 ⋅ b1) l r
    := trans_assoc l b1 b2 ⋅ ap (fun x => b2 ⋅ x) s1 ⋅ (trans_assoc t1 m b2)⁻¹
       ⋅ ap (fun x => x ⋅ t1) s2 ⋅ trans_assoc t1 t2 r.

  (** Vertical pasting. *)
  Definition vpaste {c00 c10 c01 c11 c02 c12 : C}
    {t : c00 = c10} {m : c01 = c11} {l1 : c00 = c01} {r1 : c10 = c11}
    {bo : c02 = c12} {l2 : c01 = c02} {r2 : c11 = c12}
    (s1 : Sq t m l1 r1) (s2 : Sq m bo l2 r2) : Sq t bo (l2 ⋅ l1) (r2 ⋅ r1)
    := (trans_assoc l1 l2 bo)⁻¹ ⋅ ap (fun x => x ⋅ l1) s2 ⋅ trans_assoc l1 m r2
       ⋅ ap (fun x => r2 ⋅ x) s1 ⋅ (trans_assoc t r1 r2)⁻¹.

  (** Changing the sides of a square along identifications. *)
  Definition Sq_sides {c00 c10 c01 c11 : C}
    {t t' : c00 = c10} {bo bo' : c01 = c11} {l l' : c00 = c01} {r r' : c10 = c11}
    (φt : t = t') (φb : bo = bo') (φl : l = l') (φr : r = r')
    : Sq t bo l r -> Sq t' bo' l' r'.
  Proof. destruct φt, φb, φl, φr. exact (id _). Defined.

  (** A square of loops at [c] whose sides are identified with [refl] is
      a 2-loop at [c]. *)
  Definition sq_2loop {c : C} {t bo l r : c = c}
    (et : refl = t) (eb : refl = bo) (el : refl = l) (er : refl = r)
    : Sq t bo l r -> (refl c = refl c).
  Proof. destruct et, eb, el, er. exact (id _). Defined.

  (** Transposing a square of loops inverts its 2-loop. *)
  Definition sq_2loop_inv {c : C} {t bo l r : c = c}
    (et : refl = t) (eb : refl = bo) (el : refl = l) (er : refl = r)
    (s : Sq t bo l r)
    : sq_2loop el er et eb s⁻¹ = (sq_2loop et eb el er s)⁻¹.
  Proof. destruct et, eb, el, er. exact refl. Defined.

  Definition sq_2loop_sides {c : C} {t t' bo bo' l l' r r' : c = c}
    (φt : t = t') (φb : bo = bo') (φl : l = l') (φr : r = r')
    (et : refl = t) (eb : refl = bo) (el : refl = l) (er : refl = r)
    (s : Sq t bo l r)
    : sq_2loop (φt ⋅ et) (φb ⋅ eb) (φl ⋅ el) (φr ⋅ er) (Sq_sides φt φb φl φr s)
      = sq_2loop et eb el er s.
  Proof. destruct φt, φb, φl, φr. exact refl. Defined.

  (** Composites of loops identified with [refl]. *)
  Definition eq_trans2 {c : C} {x y : c = c} (ex : refl = x) (ey : refl = y)
    : refl = y ⋅ x.
  Proof. destruct ex, ey. exact refl. Defined.

  Local Definition ap_r_refl {c : C} {x y : c = c} (s : x = y)
    : ap (fun z => z ⋅ refl) s = (trans_1p y)⁻¹ ⋅ s ⋅ trans_1p x.
  Proof. destruct s, x. exact refl. Defined.

  (** Pasting squares composes their 2-loops. *)
  Definition sq_2loop_hpaste {c : C} {t1 b1 l m t2 b2 r : c = c}
    (et1 : refl = t1) (eb1 : refl = b1) (el : refl = l) (em : refl = m)
    (et2 : refl = t2) (eb2 : refl = b2) (er : refl = r)
    (s1 : Sq t1 b1 l m) (s2 : Sq t2 b2 m r)
    : sq_2loop (eq_trans2 et1 et2) (eq_trans2 eb1 eb2) el er (hpaste s1 s2)
      = sq_2loop et1 eb1 el em s1 ⋅ sq_2loop et2 eb2 em er s2.
  Proof.
    destruct et1, eb1, el, em, et2, eb2, er. cbn.
    unfold hpaste; cbn.
    exact (ap (fun u => s1 ⋅ u) (trans_1p s2 ⋅ ap_r_refl s2)
           ⋅ ap (fun u => u ⋅ _) (ap_idmap s1)
           ⋅ ap (fun u => u ⋅ _) (trans_1p _) ⋅ trans_1p _).
  Defined.

  Definition sq_2loop_vpaste {c : C} {t m l1 r1 bo l2 r2 : c = c}
    (et : refl = t) (em : refl = m) (el1 : refl = l1) (er1 : refl = r1)
    (eb : refl = bo) (el2 : refl = l2) (er2 : refl = r2)
    (s1 : Sq t m l1 r1) (s2 : Sq m bo l2 r2)
    : sq_2loop et eb (eq_trans2 el1 el2) (eq_trans2 er1 er2) (vpaste s1 s2)
      = sq_2loop em eb el2 er2 s2 ⋅ sq_2loop et em el1 er1 s1.
  Proof.
    destruct et, em, el1, er1, eb, el2, er2. cbn.
    unfold vpaste; cbn.
    exact (ap (fun u => s2 ⋅ u) (ap_idmap s1)
           ⋅ ap (fun u => u ⋅ _) (trans_1p s2 ⋅ ap_r_refl s2)
           ⋅ ap (fun u => u ⋅ _) (trans_1p _) ⋅ trans_1p _).
  Defined.

End Squares.

(** The w-outer reading respects composition in each variable. *)
Section ReadingPaste.

  Context {A B C : Type} (F : A -> B -> C).

  Definition reading_w_hpaste {a a' a'' : A} (p : a = a') (p' : a' = a'')
    {b b' : B} (q : b = b')
    : reading_w F (p' ⋅ p) q
      = Sq_sides (ap_trans (fun z => F z b) p p')⁻¹
                 (ap_trans (fun z => F z b') p p')⁻¹ refl refl
                 (hpaste (reading_w F p q) (reading_w F p' q)).
  Proof. destruct q, p', p. exact refl. Defined.

  Definition reading_w_vpaste {a a' : A} (p : a = a')
    {b b' b'' : B} (q : b = b') (q' : b' = b'')
    : reading_w F p (q' ⋅ q)
      = Sq_sides refl refl (ap_trans (F a) q q')⁻¹ (ap_trans (F a') q q')⁻¹
                 (vpaste (reading_w F p q) (reading_w F p q')).
  Proof. destruct q', q, p. exact refl. Defined.

End ReadingPaste.

(** *** Loops: the readings as 2-loops

    For loops [p] at [a] and [q] at [b], with the sides [ap_{F(-,b)}(p)]
    and [ap_{F(a,-)}(q)] identified with [refl], the w-outer reading is
    a 2-loop at [F(a,b)].  It is bilinear, and swapping the arguments of
    [F] inverts it. *)

(** Identifications of sides with [refl] for composite loops. *)
Definition ecomp {X Y : Type} (f : X -> Y) {x : X} {p p' : x = x}
  (e : refl = ap f p) (e' : refl = ap f p') : refl = ap f (p' ⋅ p)
  := (ap_trans f p p')⁻¹ ⋅ eq_trans2 e e'.

Section LoopReadings.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Definition loops_reading (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    : refl (F a b) = refl (F a b)
    := sq_2loop eP eP eQ eQ (reading_w F p q).

  (** Bilinearity, first variable. *)
  Definition loops_reading_hpaste (p p' : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eP' : refl = ap (fun z => F z b) p')
    (eQ : refl = ap (F a) q)
    : loops_reading (p' ⋅ p) q (ecomp _ eP eP') eQ
      = loops_reading p q eP eQ ⋅ loops_reading p' q eP' eQ.
  Proof.
    unfold loops_reading.
    refine (_ ⋅ ap (sq_2loop _ _ _ _) (reading_w_hpaste F p p' q)).
    refine (_ ⋅ sq_2loop_sides _ _ refl refl _ _ eQ eQ _).
    exact (sq_2loop_hpaste eP eP eQ eQ eP' eP' eQ _ _).
  Defined.

  (** Bilinearity, second variable. *)
  Definition loops_reading_vpaste (p : a = a) (q q' : b = b)
    (eP : refl = ap (fun z => F z b) p)
    (eQ : refl = ap (F a) q) (eQ' : refl = ap (F a) q')
    : loops_reading p (q' ⋅ q) eP (ecomp _ eQ eQ')
      = loops_reading p q' eP eQ' ⋅ loops_reading p q eP eQ.
  Proof.
    unfold loops_reading.
    refine (_ ⋅ ap (sq_2loop _ _ _ _) (reading_w_vpaste F p q q')).
    refine (_ ⋅ sq_2loop_sides refl refl _ _ _ _ _ _ _).
    exact (sq_2loop_vpaste eP eP eQ eQ eP eQ' eQ' _ _).
  Defined.

End LoopReadings.

(** Swapping the arguments inverts the 2-loop. *)
Definition loops_reading_swap {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  (p : a = a) (q : b = b)
  (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
  : loops_reading (swap2 F) q p eQ eP = (loops_reading F p q eP eQ)⁻¹.
Proof.
  unfold loops_reading.
  refine (_ ⋅ ap (sq_2loop eQ eQ eP eP) (reading_w_swap F p q)).
  exact (sq_2loop_inv eP eP eQ eQ (reading_w F p q)).
Defined.


(** *** The case of [TBD2]: [loop³] and [loop²]

    Let [F : S¹ → S¹ → C] with the sides [ap_{F(-,base)}(loop)] and
    [ap_{F(base,-)}(loop)] identified with [refl] (for [F(z,w) :≡ m(z)(w)]
    these are [ptw(m(loop))(base) = m_loop(base) ≡ refl] and
    [ap_{cst}(loop) = refl]), and let [γ] be the 2-loop of [F(loop,loop)].
    Then the w-outer reading of [F(loop³,loop²)] is [6γ], and the
    z-outer one, which is [apd] of [z ↦ ap_{F(z,-)}(loop²)] applied to
    [loop³], is its inverse. *)
Section Loop3Loop2.

  Context {C : Type} (F : S1 -> S1 -> C)
    (eP : refl = ap (fun z => F z base) loop) (eQ : refl = ap (F base) loop).

  Definition loop2 : base = base := loop ⋅ loop.
  Definition loop3 : base = base := loop ⋅ loop2.

  Definition eP3 : refl = ap (fun z => F z base) loop3
    := ecomp _ (ecomp _ eP eP) eP.
  Definition eQ2 : refl = ap (F base) loop2 := ecomp _ eQ eQ.

  Definition γ : refl (F base base) = refl (F base base)
    := loops_reading F loop loop eP eQ.

  Definition loop1_loop2_reading
    : loops_reading F loop loop2 eP eQ2 = γ ⋅ γ
    := loops_reading_vpaste F loop loop loop eP eQ eQ.

  Definition loop3_loop2_reading
    : loops_reading F loop3 loop2 eP3 eQ2 = ((γ ⋅ γ) ⋅ (γ ⋅ γ)) ⋅ (γ ⋅ γ).
  Proof.
    refine (_ ⋅ loops_reading_hpaste F loop2 loop loop2 (ecomp _ eP eP) eP eQ2).
    exact (ap (fun u => (u ⋅ u) ⋅ u) loop1_loop2_reading
           ⋅ ap (fun u => u ⋅ _) (loops_reading_hpaste F loop loop loop2 eP eP eQ2)).
  Defined.

  (** The z-outer reading: [(6γ)⁻¹]. *)
  Definition loop3_loop2_reading_z
    : loops_reading (swap2 F) loop2 loop3 eQ2 eP3
      = (((γ ⋅ γ) ⋅ (γ ⋅ γ)) ⋅ (γ ⋅ γ))⁻¹
    := ap symm loop3_loop2_reading ⋅ loops_reading_swap F loop3 loop2 eP3 eQ2.

End Loop3Loop2.

(** *** Precomposition and powers, for [TBD1] *)

Local Definition ap_comp {X Y Z : Type} (f : X -> Y) (h : Y -> Z)
  {x x' : X} (p : x = x') : ap (fun z => h (f z)) p = ap h (ap f p)
  := match p with refl => refl end.

Section Precomposition.

  Context {A A' B B' C : Type} (F : A -> B -> C).

  (** Precomposition in the first variable. *)
  Definition reading_w_precomp1 (f : A' -> A) {a a' : A'} (p : a = a')
    {b b' : B} (q : b = b')
    : Sq_sides (ap_comp f (fun x => F x b) p) (ap_comp f (fun x => F x b') p)
               refl refl (reading_w (fun z w => F (f z) w) p q)
      = reading_w F (ap f p) q.
  Proof. destruct p, q. exact refl. Defined.

  (** Precomposition in the second variable. *)
  Definition reading_w_precomp2 (g : B' -> B) {a a' : A} (p : a = a')
    {b b' : B'} (q : b = b')
    : Sq_sides refl refl (ap_comp g (F a) q) (ap_comp g (F a') q)
               (reading_w (fun z w => F z (g w)) p q)
      = reading_w F p (ap g q).
  Proof. destruct p, q. exact refl. Defined.

  Definition loops_reading_precomp1 (f : A' -> A) {a : A'} {b : B}
    (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F (f z) b) p) (eQ : refl = ap (F (f a)) q)
    : loops_reading (fun z w => F (f z) w) p q eP eQ
      = loops_reading F (ap f p) q (ap_comp f (fun x => F x b) p ⋅ eP) eQ
    := ap (sq_2loop _ _ eQ eQ) (reading_w_precomp1 f p q)
       ⋅ (sq_2loop_sides _ _ refl refl eP eP eQ eQ _)⁻¹.

  Definition loops_reading_precomp2 (g : B' -> B) {a : A} {b : B'}
    (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z (g b)) p) (eQ : refl = ap (fun w => F a (g w)) q)
    : loops_reading (fun z w => F z (g w)) p q eP eQ
      = loops_reading F p (ap g q) eP (ap_comp g (F a) q ⋅ eQ)
    := ap (sq_2loop eP eP _ _) (reading_w_precomp2 g p q)
       ⋅ (sq_2loop_sides refl refl _ _ eP eP eQ eQ _)⁻¹.

End Precomposition.

(** Transporting the loops along identifications. *)
Definition loops_reading_tr1 {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  {p p' : a = a} (α : p = p') (q : b = b)
  (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
  : loops_reading F p q eP eQ = loops_reading F p' q (ap (ap _) α ⋅ eP) eQ.
Proof. destruct α. exact refl. Defined.

Definition loops_reading_tr2 {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  (p : a = a) {q q' : b = b} (β : q = q')
  (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
  : loops_reading F p q eP eQ = loops_reading F p q' eP (ap (ap _) β ⋅ eQ).
Proof. destruct β. exact refl. Defined.

(** Powers [p^n] of a loop, with [p^{n+1} :≡ p ⋅ p^n], and of 2-loops. *)
Fixpoint ppow {X : Type} {x : X} (p : x = x) (n : nat) : x = x
  := match n with O => refl | S n => p ⋅ ppow p n end.

Fixpoint eppow {X Y : Type} (f : X -> Y) {x : X} {p : x = x}
  (e : refl = ap f p) (n : nat) : refl = ap f (ppow p n)
  := match n with O => refl | S n => ecomp f (eppow f e n) e end.

Definition gpow_comm {X : Type} {x : X} {y : x = x} (γ : y = y) (n : nat)
  : ppow γ n ⋅ γ = γ ⋅ ppow γ n.
Proof.
  induction n as [|n IH]; cbn.
  - exact (trans_1p γ)⁻¹.
  - exact (ap (fun u => γ ⋅ u) IH ⋅ (trans_assoc _ _ _)⁻¹).
Defined.

Section Powers.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Local Definition sq_2loop_l {c : C} {l : c = c} (e : refl = l)
    : sq_2loop refl refl e e (trans_1p l) = refl.
  Proof. destruct e. exact refl. Defined.

  Local Definition sq_2loop_t {c : C} {t : c = c} (e : refl = t)
    : sq_2loop e e refl refl ((trans_1p t)⁻¹ ⋅ refl) = refl.
  Proof. destruct e. exact refl. Defined.

  Local Definition reading_w_refl1 {b' : B} (q : b = b')
    : reading_w F (refl a) q = trans_1p (ap (F a) q).
  Proof. destruct q. exact refl. Defined.

  (** [F(p^n,q)] has [n] times the 2-loop of [F(p,q)]. *)
  Definition loops_reading_pow1 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (n : nat)
    : loops_reading F (ppow p n) q (eppow _ eP n) eQ
      = ppow (loops_reading F p q eP eQ) n.
  Proof.
    induction n as [|n IH].
    - exact (sq_2loop_l eQ ⋅ ap (sq_2loop refl refl eQ eQ) (reading_w_refl1 q)).
    - exact (gpow_comm _ n ⋅ ap (fun u => u ⋅ _) IH
             ⋅ loops_reading_hpaste F (ppow p n) p q (eppow _ eP n) eP eQ).
  Defined.

  (** [F(p,q^n)] has [n] times the 2-loop of [F(p,q)]. *)
  Definition loops_reading_pow2 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (n : nat)
    : loops_reading F p (ppow q n) eP (eppow _ eQ n)
      = ppow (loops_reading F p q eP eQ) n.
  Proof.
    induction n as [|n IH].
    - exact (sq_2loop_t eP).
    - exact (ap (fun u => _ ⋅ u) IH
             ⋅ loops_reading_vpaste F p (ppow q n) q eP (eppow _ eQ n) eQ).
  Defined.

End Powers.

(** [TBD1]: precomposing with the degree [k] map [dg_k] in either
    variable multiplies the 2-loop of [F(loop,loop)] by [k]. *)
Section DegreePrecomposition.

  Context `{Univalence} {C : Type} (F : S1 -> S1 -> C)
    (eP : refl = ap (fun z => F z base) loop) (eQ : refl = ap (F base) loop)
    (k : nat).

  Definition loopZ_ppow (n : nat) : loopZ (iplus n) = ppow loop n.
  Proof.
    induction n as [|n IH].
    - exact refl.
    - exact (ap (fun u => loop ⋅ u) IH ⋅ loopZ_zs (iplus n)).
  Defined.

  Definition dg_loop : ap (dg k) loop = ppow loop k
    := loopZ_ppow k ⋅ S1_rec_loop S1 base (loopZ (iplus k)).

  Local Definition cancel {Y : Type} {r t0 t1 t2 : Y}
    (α : t1 = t0) (φ : t2 = t1) (E : r = t0)
    : α ⋅ (φ ⋅ (φ⁻¹ ⋅ α⁻¹ ⋅ E)) = E.
  Proof. destruct φ, α. exact refl. Defined.

  (** The sides of [F ∘ (dg_k × id)] and [F ∘ (id × dg_k)]. *)
  Definition eP_dg1 : refl = ap (fun z => F (dg k z) base) loop
    := (ap_comp (dg k) (fun x => F x base) loop)⁻¹
       ⋅ (ap (ap (fun x => F x base)) dg_loop)⁻¹ ⋅ eppow _ eP k.

  Definition eQ_dg2 : refl = ap (fun w => F base (dg k w)) loop
    := (ap_comp (dg k) (F base) loop)⁻¹
       ⋅ (ap (ap (F base)) dg_loop)⁻¹ ⋅ eppow _ eQ k.

  Definition loops_reading_dg1
    : loops_reading (fun z w => F (dg k z) w) loop loop eP_dg1 eQ
      = ppow (loops_reading F loop loop eP eQ) k
    := loops_reading_pow1 F loop loop eP eQ k
       ⋅ ap (fun e => loops_reading F (ppow loop k) loop e eQ) (cancel _ _ _)
       ⋅ loops_reading_tr1 F dg_loop loop _ eQ
       ⋅ loops_reading_precomp1 F (dg k) loop loop eP_dg1 eQ.

  Definition loops_reading_dg2
    : loops_reading (fun z w => F z (dg k w)) loop loop eP eQ_dg2
      = ppow (loops_reading F loop loop eP eQ) k
    := loops_reading_pow2 F loop loop eP eQ k
       ⋅ ap (fun e => loops_reading F loop (ppow loop k) eP e) (cancel _ _ _)
       ⋅ loops_reading_tr2 F loop dg_loop eP _
       ⋅ loops_reading_precomp2 F (dg k) loop loop eP eQ_dg2.

End DegreePrecomposition.

(** *** Independence of the side identifications, and negative degrees

    The 2-loop of a square of loops does not depend on how its sides are
    identified with [refl]: changing them conjugates it, and 2-loops
    commute (Eckmann-Hilton). *)
Section Independence.

  Context {C : Type} {c : C}.

  Local Definition sq_2loop_conj {t l : c = c} (e : refl = t) (f : refl = l)
    (s : Sq t t l l)
    : sq_2loop e e f f s
      = (ap011 (fun x y : c = c => y ⋅ x) f e)⁻¹
        ⋅ (s ⋅ ap011 (fun x y : c = c => y ⋅ x) e f).
  Proof. destruct e, f. exact (trans_1p s)⁻¹. Defined.

  Local Definition ap011_split {x x' y y' : c = c} (α : x = x') (β : y = y')
    : ap011 (fun x y : c = c => y ⋅ x) α β
      = ap (fun x => y ⋅ x) α @ ap (fun y => y ⋅ x') β.
  Proof. destruct α, β. exact refl. Defined.

  Local Definition ap_trans_refl {y y' : c = c} (β : y = y')
    : ap (fun z : c = c => z ⋅ refl) β = trans_1p y @ β @ (trans_1p y')^.
  Proof. destruct β. exact (whiskerR (concat_p1 _) _ @ concat_pV _)^. Defined.

  Local Definition ap011_2loops (α β : refl c = refl c :> (c = c))
    : ap011 (fun x y : c = c => y ⋅ x) α β = α @ β.
  Proof.
    refine (ap011_split α β @ _).
    refine (ap (fun u => u @ _) (ap_idmap α) @ _).
    exact (ap (fun u => α @ u) (ap_trans_refl β @ concat_p1 _ @ concat_1p _)).
  Defined.

  Definition sq_2loop_2loops (e f : refl c = refl c :> (c = c))
    (s : Sq (refl c) (refl c) (refl c) (refl c))
    : sq_2loop e e f f s = s.
  Proof.
    refine (sq_2loop_conj e f s @ _).
    refine (trans_is_concat _ _ @ _).
    refine (ap (fun u => u @ _) (trans_is_concat _ _) @ _).
    refine (ap (fun u => (_ @ s) @ u^) (ap011_2loops f e @ eckmann_hilton f e) @ _).
    refine (ap (fun u => (u @ s) @ _) (ap011_2loops e f) @ _).
    refine (ap (fun u => u @ _) (eckmann_hilton _ s) @ _).
    exact (concat_pp_V _ _).
  Defined.

  Definition sq_2loop_indep {t l : c = c} (e e' : refl = t) (f f' : refl = l)
    (s : Sq t t l l)
    : sq_2loop e e f f s = sq_2loop e' e' f' f' s.
  Proof. destruct e, f. exact (sq_2loop_2loops e' f' s)^. Defined.

End Independence.

Definition loops_reading_indep {A B C : Type} (F : A -> B -> C) {a : A} {b : B}
  (p : a = a) (q : b = b)
  (eP eP' : refl = ap (fun z => F z b) p) (eQ eQ' : refl = ap (F a) q)
  : loops_reading F p q eP eQ = loops_reading F p q eP' eQ'
  := sq_2loop_indep _ _ _ _ _.

(** Inverse loops give inverse 2-loops. *)
Section Inverses.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Definition einv {X Y : Type} (f : X -> Y) {x : X} {p : x = x}
    (e : refl = ap f p) : refl = ap f p⁻¹
    := (ap_V f p)^ ⋅ ap inverse e.

  Local Definition cancel_r {X : Type} {x : X} {u v : x = x} (h : refl = v @ u)
    : v = u^
    := (concat_p1 _)^ @ whiskerL _ (concat_pV u)^ @ concat_p_pp _ _ _
       @ whiskerR h^ _ @ concat_1p _.

  Local Definition cancel_l {X : Type} {x : X} {u v : x = x} (h : refl = u @ v)
    : v = u^
    := (concat_1p _)^ @ whiskerR (concat_Vp u)^ _ @ concat_pp_p _ _ _
       @ whiskerL _ h^ @ concat_p1 _.

  Definition loops_reading_inv1 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    (eP' : refl = ap (fun z => F z b) p⁻¹)
    : loops_reading F p⁻¹ q eP' eQ = (loops_reading F p q eP eQ)⁻¹.
  Proof.
    apply cancel_r.
    refine (_ @ trans_is_concat _ _).
    refine (_ @ loops_reading_hpaste F p p⁻¹ q eP eP' eQ).
    refine (_ @ (loops_reading_tr1 F (trans_pV p) q _ eQ)^).
    exact ((loops_reading_pow1 F p q eP eQ 0)^ @ loops_reading_indep F _ q _ _ eQ eQ).
  Defined.

  Definition loops_reading_inv2 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    (eQ' : refl = ap (F a) q⁻¹)
    : loops_reading F p q⁻¹ eP eQ' = (loops_reading F p q eP eQ)⁻¹.
  Proof.
    apply cancel_l.
    refine (_ @ trans_is_concat _ _).
    refine (_ @ loops_reading_vpaste F p q q⁻¹ eP eQ eQ').
    refine (_ @ (loops_reading_tr2 F p (trans_pV q) eP _)^).
    exact ((loops_reading_pow2 F p q eP eQ 0)^ @ loops_reading_indep F p _ eP eP _ _).
  Defined.

End Inverses.

(** Integer powers [p^z] ([loopexp]) multiply the 2-loop by [z]. *)
Section IntPowers.

  Context {A B C : Type} (F : A -> B -> C) {a : A} {b : B}.

  Definition eloopexp {X Y : Type} (f : X -> Y) {x : X} {p : x = x}
    (e : refl = ap f p) (z : Int) : refl = ap f (loopexp p z).
  Proof.
    induction z as [|n IH|n IH].
    - exact refl.
    - exact ((ap (ap f) (loopexp_succ_r p n @ (trans_is_concat _ _)^))⁻¹ ⋅ ecomp f IH e).
    - exact ((ap (ap f) (loopexp_pred_r p _ @ (trans_is_concat _ _)^))⁻¹
             ⋅ ecomp f IH (einv f e)).
  Defined.

  Definition loops_reading_loopexp1 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (z : Int)
    (e : refl = ap (fun z => F z b) (loopexp p z))
    : loops_reading F (loopexp p z) q e eQ = loopexp (loops_reading F p q eP eQ) z.
  Proof.
    revert e. induction z as [|n IH|n IH]; intro e.
    - exact (loops_reading_indep F _ q e refl eQ eQ @ loops_reading_pow1 F p q eP eQ 0).
    - refine (loops_reading_tr1 F (loopexp_succ_r p n @ (trans_is_concat _ _)^) q e eQ @ _).
      refine (loops_reading_indep F _ q _ (ecomp _ (eloopexp _ eP n) eP) eQ eQ @ _).
      refine (loops_reading_hpaste F _ p q _ eP eQ @ trans_is_concat _ _ @ _).
      exact (ap (fun u => _ @ u) (IH _) @ (loopexp_succ_l _ n)^).
    - refine (loops_reading_tr1 F (loopexp_pred_r p _ @ (trans_is_concat _ _)^) q e eQ @ _).
      refine (loops_reading_indep F _ q _
                (ecomp _ (eloopexp _ eP _) (einv _ eP)) eQ eQ @ _).
      refine (loops_reading_hpaste F _ p⁻¹ q _ _ eQ @ trans_is_concat _ _ @ _).
      refine (ap (fun u => u @ _) (loops_reading_inv1 F p q eP eQ _) @ _).
      exact (ap (fun u => _ @ u) (IH _) @ (loopexp_pred_l _ _)^).
  Defined.

  Definition loops_reading_loopexp2 (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q) (z : Int)
    (e : refl = ap (F a) (loopexp q z))
    : loops_reading F p (loopexp q z) eP e = loopexp (loops_reading F p q eP eQ) z.
  Proof.
    revert e. induction z as [|n IH|n IH]; intro e.
    - exact (loops_reading_indep F p _ eP eP e refl @ loops_reading_pow2 F p q eP eQ 0).
    - refine (loops_reading_tr2 F p (loopexp_succ_r q n @ (trans_is_concat _ _)^) eP e @ _).
      refine (loops_reading_indep F p _ eP eP _ (ecomp _ (eloopexp _ eQ n) eQ) @ _).
      refine (loops_reading_vpaste F p _ q eP _ eQ @ trans_is_concat _ _ @ _).
      exact (ap (fun u => u @ _) (IH _) @ (loopexp_succ_r _ n)^).
    - refine (loops_reading_tr2 F p (loopexp_pred_r q _ @ (trans_is_concat _ _)^) eP e @ _).
      refine (loops_reading_indep F p _ eP eP _
                (ecomp _ (eloopexp _ eQ _) (einv _ eQ)) @ _).
      refine (loops_reading_vpaste F p _ q⁻¹ eP _ _ @ trans_is_concat _ _ @ _).
      refine (ap (fun u => _ @ u) (loops_reading_inv2 F p q eP eQ _) @ _).
      exact (ap (fun u => u @ _) (IH _) @ (loopexp_pred_r _ _)^).
  Defined.

End IntPowers.

(** The degree [k] map for all [k : ℤ] ([dg] of [def:dgm-map] is
    [dgZ ∘ ι₊] by definition), and precomposition with it. *)
Definition dgZ `{Univalence} (k : ℤ) : S1 -> S1 := S1_rec S1 base (loopZ k).

Definition dg_dgZ `{Univalence} (n : nat) : dg n = dgZ (iplus n) := refl.

Section IntDegrees.

  Context `{Univalence} {C : Type} (F : S1 -> S1 -> C)
    (eP : refl = ap (fun z => F z base) loop) (eQ : refl = ap (F base) loop)
    (k : ℤ).

  Definition dgZ_loop : ap (dgZ k) loop = loopexp loop (toInt k)
    := S1_rec_loop S1 base (loopZ k).

  Definition loops_reading_dgZ1 (eP' : refl = ap (fun z => F (dgZ k z) base) loop)
    : loops_reading (fun z w => F (dgZ k z) w) loop loop eP' eQ
      = loopexp (loops_reading F loop loop eP eQ) (toInt k)
    := loops_reading_precomp1 F (dgZ k) loop loop eP' eQ
       @ loops_reading_tr1 F dgZ_loop loop _ eQ
       @ loops_reading_loopexp1 F loop loop eP eQ (toInt k) _.

  Definition loops_reading_dgZ2 (eQ' : refl = ap (fun w => F base (dgZ k w)) loop)
    : loops_reading (fun z w => F z (dgZ k w)) loop loop eP eQ'
      = loopexp (loops_reading F loop loop eP eQ) (toInt k)
    := loops_reading_precomp2 F (dgZ k) loop loop eP eQ'
       @ loops_reading_tr2 F loop dgZ_loop eP _
       @ loops_reading_loopexp2 F loop loop eP eQ (toInt k) _.

End IntDegrees.

(** *** The w-outer reading of a map [m : S¹ →* (S¹ →* B)]

    For a loop [ℓ] at the constant pointed map, and [m :≡ evp⁻¹(ℓ)]
    (so [m(base) :≡ cst], [m(loop) = ℓ], [m_pt :≡ refl]), the w-outer
    reading of [F(z,w) :≡ m(z)(w)] at [(loop,loop)] is [evp] of the
    pointed map [S¹ →* ΩB] corresponding to [ℓ]. *)


(** The w-outer reading of [G(p,q)] in terms of a path [φ] of functions
    identified with [ap_G(p)]. *)
Definition beta_w {A B C : Type} (G : A -> B -> C) {a a' : A} (p : a = a')
  {φ : G a = G a'} (θ : ap G p = φ) (w : B)
  : apD10 φ w = ap (fun z => G z w) p.
Proof. destruct θ, p. exact refl. Defined.

Definition reading_w_fun {A B C : Type} (G : A -> B -> C) {a a' : A}
  (p : a = a') {φ : G a = G a'} (θ : ap G p = φ) {b b' : B} (q : b = b')
  : reading_w G p q
    = Sq_sides (beta_w G p θ b) (beta_w G p θ b') refl refl
        (po_sq (u := G a) (v := G a') q (apd (apD10 φ) q)).
Proof. destruct θ, p, q. exact refl. Defined.

Local Definition sq_2loop_t1 {C : Type} {c : C} {t : c = c} (et : refl = t)
  (s : Sq t refl refl refl) : sq_2loop et refl refl refl s = s ⋅ et.
Proof. destruct et. exact (trans_1p s)⁻¹. Defined.

(** For a constant function the reading of a homotopy [h] is [ap_h],
    conjugated by the identifications of its ends with [refl]. *)
Definition const_reading {B C : Type} (c0 : C) (h : B -> c0 = c0)
  {b b' : B} (q : b = b') (et : refl = h b) (eb : refl = h b')
  : sq_2loop et eb (ap_const q c0)⁻¹ (ap_const q c0)⁻¹
      (po_sq (u := fun _ => c0) (v := fun _ => c0) q (apd h q))
    = eb⁻¹ ⋅ (ap h q ⋅ et).
Proof.
  destruct q. cbn. revert et eb. generalize (h b). intros t et eb.
  destruct eb. exact (sq_2loop_t1 et refl).
Defined.

Section PtdReading.

  Context `{Funext} (B : Ustar).

  Local Notation c := (pt (pmap_ptd S1star B)).

  Local Definition trp_pt_eqv {f g : S1 -> utype B} (φ : f = g)
    (u : pt B = f base) (v : pt B = g base)
    : (transport (fun f => pt B = f base) φ u = v) <~> (v = apD10 φ base ⋅ u).
  Proof. destruct φ. exact (equiv_path_inverse _ _). Defined.

  (** [ptw_*] at the constant map, directly: a loop [ℓ] at [c] goes to
      [(apD10(ap_fst(ℓ)), e)] with [e : refl = apD10(ap_fst(ℓ))(base)]. *)
  Definition lc_eqv : (c = c) ≃ (S1star →* loops B).
  Proof.
    apply Eqv_of_Equiv.
    refine (equiv_compose' _ (equiv_path_sigma _ c c)^-1).
    refine (equiv_functor_sigma' (equiv_apD10 _ _ _) _).
    intro φ. cbn.
    exact (equiv_compose' (equiv_concat_r (trans_1p _) _) (trp_pt_eqv φ refl refl)).
  Defined.

  Definition F_of (ℓ : c = c) : S1 -> S1 -> utype B
    := fun z w => fst (S1_rec _ c ℓ z) w.

  Definition theta_of (ℓ : c = c)
    : ap (fun z => fst (S1_rec _ c ℓ z)) loop = ap fst ℓ
    := ap_compose (S1_rec _ c ℓ) fst loop @ ap (ap fst) (S1_rec_loop _ c ℓ).

  Definition eP_of (ℓ : c = c) : refl = ap (fun z => F_of ℓ z base) loop
    := beta_w (fun z => fst (S1_rec _ c ℓ z)) loop (theta_of ℓ) base
       ⋅ snd (fst lc_eqv ℓ).

  Definition eQ_of (ℓ : c = c) : refl = ap (F_of ℓ base) loop
    := (ap_const loop (pt B))⁻¹.

  (** The w-outer reading of [F_of ℓ] at [(loop,loop)] is [evp] of the
      pointed map corresponding to [ℓ]. *)
  Definition reading_lc (ℓ : c = c)
    : loops_reading (F_of ℓ) loop loop (eP_of ℓ) (eQ_of ℓ)
      = evp _ (fst lc_eqv ℓ).
  Proof.
    unfold loops_reading.
    refine (ap (sq_2loop _ _ _ _)
              (reading_w_fun (fun z => fst (S1_rec _ c ℓ z)) loop (theta_of ℓ) loop) @ _).
    refine (sq_2loop_sides _ _ refl refl _ _ _ _ _ @ _).
    exact (const_reading (pt B) (apD10 (ap fst ℓ)) loop _ _).
  Defined.

End PtdReading.

(** The equivalence [M ≃ ℤ] of Example [exa:allS1*-swap]. *)
Section MEqvZ.

  Context `{Univalence}.

  (** [B²ℤ :≡ Σ_{X:U} ‖S¹ = X‖₀], pointed at [(S¹,|refl|)]. *)
  Definition B2Z : Ustar := ({X : Type & Tr 0 (S1 = X)}; (S1; tr refl)).

  Definition M : Type := S1star →* pmap_ptd S1star B2Z.

  (** Evaluation at [loop] ([evp], [cor:circle-loopspace]). *)
  Definition M_eqv_loops
    : M ≃ (pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z))
    := (evp _; evp_isEquiv _).

  (** [ptw_*] ([con:identity-ptd-maps]) at the constant map, as
      [lc_eqv]. *)
  Definition loops_cst_eqv
    : (pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z))
      ≃ (S1star →* loops B2Z)
    := lc_eqv B2Z.

  Definition omega2_eqv
    : (S1star →* loops B2Z) ≃ (refl (pt B2Z) = refl (pt B2Z))
    := (evp _; evp_isEquiv _).

  (** [Ω²B²ℤ ≃ (refl_{S¹} = refl_{S¹})]: the second component of a
      loop at [pt] is a path in the set [‖S¹ = S¹‖₀]. *)
  Definition sigma_step : (refl (pt B2Z) = refl (pt B2Z)) ≃ (refl S1 = refl S1).
  Proof.
    apply Eqv_of_Equiv.
    refine (equiv_compose' (equiv_path_sigma_hprop
      (P := fun p : S1 = S1 => transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr refl)
      (refl; refl) (refl; refl))^-1 _).
    exact (equiv_ap (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 refl refl).
  Defined.

  (** [(refl_{S¹} = refl_{S¹}) ≃ (id_{S¹} = id_{S¹})]: univalence, and
      that [equiv_fun] is an embedding. *)
  Definition ua0_step : (refl S1 = refl S1) ≃ ((fun x : S1 => x) = (fun x => x)).
  Proof.
    apply Eqv_of_Equiv.
    refine (equiv_compose' (Build_Equiv _ _ (ap (x := equiv_path S1 S1 refl)
              (y := equiv_path S1 S1 refl) (@equiv_fun S1 S1)) _) _).
    exact (equiv_ap (equiv_equiv_path S1 S1) refl refl).
  Defined.

  (** [(id_{S¹} = id_{S¹}) ≃ ∏_x (x = x)]: function extensionality. *)
  Definition funext_step : ((fun x : S1 => x) = (fun x => x)) ≃ (forall x : S1, x = x)
    := Eqv_of_Equiv (equiv_path_forall (fun x : S1 => x) (fun x => x))^-1.

  Definition ua_step : (refl S1 = refl S1) ≃ (forall x : S1, x = x)
    := Eqv_comp ua0_step funext_step.

  (** [∏_x (x = x) ≃ (base = base)]: evaluation at [base]
      ([xca:(S1->S1)_(f)-eqv-S1]). *)
  Definition ev_step : (forall x : S1, x = x) ≃ (base = base)
    := Eqv_of_Equiv (Build_Equiv _ _ _ (ev_base_S1_isEquiv idmap)).

  Definition omega2_B2Z_eqv : (refl (pt B2Z) = refl (pt B2Z)) ≃ ℤ
    := Eqv_comp sigma_step (Eqv_comp ua_step (Eqv_comp ev_step wdg)).

  Definition M_eqv_Z : M ≃ ℤ
    := Eqv_comp M_eqv_loops
         (Eqv_comp loops_cst_eqv (Eqv_comp omega2_eqv omega2_B2Z_eqv)).

  (** The maps [m_k : M] of the example, for [k : ℤ].  First the
      [k]-loop around [id_S¹]: pointwise it is [x ↦ ex(x)(loop^k)]
      ([ext_base_S1], the rotation extending [loop^k]); by function
      extensionality and univalence it is a 2-loop at [refl_{S¹}], and
      hence at [refl_{pt}] in [B²ℤ] (the truncated component being a
      set). *)
  Definition kloop_pw (k : ℤ) : forall x : S1, x = x
    := ext_base_S1 idmap (loopZ k).

  Definition kloop_id (k : ℤ) : refl S1 = refl S1
    := eqinv (snd ua_step) (kloop_pw k).

  Definition kloop (k : ℤ) : refl (pt B2Z) = refl (pt B2Z)
    := eqinv (snd sigma_step) (kloop_id k).

  (** [dg_k' : S¹ →* ΩB²ℤ], with [dg_k'(base) :≡ refl_{pt}],
      [dg_k'(loop) := kloop k], pointed by reflexivity. *)
  Definition dg_k' (k : ℤ) : S1star →* loops B2Z := evp_inv _ (kloop k).

  (** [m_k(base) :≡ pt], [m_k(loop) := ptw_*⁻¹(dg_k')] (with the
      pointing condition of [dg_k'] turned around as in
      [loops_cst_eqv]), [(m_k)_pt :≡ refl]. *)
  Definition m_k (k : ℤ) : M := evp_inv _ (eqinv (snd loops_cst_eqv) (dg_k' k)).

  Definition evp_evp_inv {A : Type} (a : A) (l : a = a) : evp a (evp_inv a l) = l
    := trans_1p _ @ S1_rec_loop A a l.

  Definition omega2_kloop (k : ℤ) : fst omega2_B2Z_eqv (kloop k) = k.
  Proof.
    change (fst wdg (fst ev_step (fst ua_step (fst sigma_step
              (eqinv (snd sigma_step) (kloop_id k))))) = k).
    refine (ap (fun x => fst wdg (fst ev_step (fst ua_step x)))
              (eqinv_r (snd sigma_step) _) @ _).
    refine (ap (fun x => fst wdg (fst ev_step x)) (eqinv_r (snd ua_step) _) @ _).
    exact (wdg_loopZ k).
  Defined.

  (** [M_eqv_Z] sends [m_k] to [k]. *)
  Definition M_eqv_Z_m (k : ℤ) : fst M_eqv_Z (m_k k) = k.
  Proof.
    change (fst omega2_B2Z_eqv (fst omega2_eqv (fst loops_cst_eqv
              (evp _ (evp_inv _ (eqinv (snd loops_cst_eqv) (dg_k' k)))))) = k).
    refine (ap (fun l => fst omega2_B2Z_eqv (fst omega2_eqv (fst loops_cst_eqv l)))
              (evp_evp_inv _ _) @ _).
    refine (ap (fun d => fst omega2_B2Z_eqv (fst omega2_eqv d))
              (eqinv_r (snd loops_cst_eqv) _) @ _).
    refine (ap (fst omega2_B2Z_eqv) (evp_evp_inv _ _) @ _).
    exact (omega2_kloop k).
  Defined.

  (** The w-outer reading of [m_k] (pointing paths forgotten,
      [F(z,w) :≡ m_k(z)(w)]) at [(loop,loop)] is the [k]-loop around
      [id_S¹], with the sides identified with [refl] by [eP_of] (from
      the pointing of [dg_k']) and [eQ_of] ([ap] of a constant). *)
  Definition ell_k (k : ℤ) : pt (pmap_ptd S1star B2Z) = pt (pmap_ptd S1star B2Z)
    := eqinv (snd loops_cst_eqv) (dg_k' k).

  Definition reading_m_k (k : ℤ)
    : loops_reading (fun z w => fst (fst (m_k k) z) w) loop loop
        (eP_of B2Z (ell_k k)) (eQ_of B2Z (ell_k k))
      = kloop k
    := reading_lc B2Z (ell_k k)
       @ ap (evp _) (eqinv_r (snd loops_cst_eqv) (dg_k' k))
       @ evp_evp_inv _ _.

  (** Hence it corresponds to [k] under [Ω²B²ℤ ≃ ℤ]. *)
  Definition reading_m_k_Z (k : ℤ)
    : fst omega2_B2Z_eqv
        (loops_reading (fun z w => fst (fst (m_k k) z) w) loop loop
           (eP_of B2Z (ell_k k)) (eQ_of B2Z (ell_k k)))
      = k
    := ap (fst omega2_B2Z_eqv) (reading_m_k k) @ omega2_kloop k.

  (** The composite of [sigma_step], [ua_step] and [ev_step] as a
      single [ap]: it sends a 2-loop [x] to [ap] of
      [r ↦ ptoe(ap_fst(r))(base)] at [x]; so it preserves powers. *)
  Definition Psi (x : refl (pt B2Z) = refl (pt B2Z)) : base = base
    := ap (fun r : pt B2Z = pt B2Z => transport idmap (ap pr1 r) base) x.

  Local Definition inv_path_sigma_hprop_pr1 {A : Type} {P : A -> Type}
    `{forall x, IsHProp (P x)} (u v : sig P) (r : u = v)
    : (equiv_path_sigma_hprop u v)^-1 r = ap pr1 r
    := (pr1_path_path_sigma_hprop u v _)^
       @ ap (fun r => r..1) (eisretr (path_sigma_hprop u v) r).

  Local Definition apD10_ap_ev {X Y : Type} {f g : X -> Y} (q : f = g) (x : X)
    : apD10 q x = ap (fun h => h x) q.
  Proof. destruct q. exact refl. Defined.

  Local Definition ap5 {A1 A2 A3 A4 A5 A6 : Type} (h1 : A1 -> A2) (h2 : A2 -> A3)
    (h3 : A3 -> A4) (h4 : A4 -> A5) (h5 : A5 -> A6) {a a' : A1} (x : a = a')
    : ap (fun r => h5 (h4 (h3 (h2 (h1 r))))) x = ap h5 (ap h4 (ap h3 (ap h2 (ap h1 x)))).
  Proof. destruct x. exact refl. Defined.

  Definition Psi_eq (x : refl (pt B2Z) = refl (pt B2Z))
    : Psi x = fst ev_step (fst ua_step (fst sigma_step x)).
  Proof.
    change (Psi x = apD10 (ap (@equiv_fun S1 S1) (ap (equiv_path S1 S1)
              ((equiv_path_sigma_hprop
                (P := fun p : S1 = S1 => transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr refl)
                (refl; refl) (refl; refl))^-1
                 (ap (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 x)))) base).
    refine (_ @ (apD10_ap_ev _ base)^).
    refine (_ @ (ap (fun y => ap (fun h : S1 -> S1 => h base)
                   (ap (@equiv_fun S1 S1) (ap (equiv_path S1 S1) y)))
                   (inv_path_sigma_hprop_pr1 _ _ _))^).
    exact (ap5 (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 pr1 (equiv_path S1 S1)
             (@equiv_fun S1 S1) (fun h : S1 -> S1 => h base) x).
  Defined.

  Definition Psi_inj {x y : refl (pt B2Z) = refl (pt B2Z)} (e : Psi x = Psi y) : x = y.
  Proof.
    pose (E := Eqv_comp sigma_step (Eqv_comp ua_step ev_step)).
    refine ((eqinv_l (snd E) x)^ @ _ @ eqinv_l (snd E) y).
    exact (ap (eqinv (snd E)) ((Psi_eq x)^ @ e @ Psi_eq y)).
  Defined.

  Definition Psi_kloop (k : ℤ) : Psi (kloop k) = loopZ k.
  Proof.
    refine (Psi_eq _ @ _).
    change (fst ev_step (fst ua_step (fst sigma_step
              (eqinv (snd sigma_step) (kloop_id k)))) = loopZ k).
    refine (ap (fun x => fst ev_step (fst ua_step x)) (eqinv_r (snd sigma_step) _) @ _).
    exact (ap (fst ev_step) (eqinv_r (snd ua_step) _)).
  Defined.

  (** [γ :≡ kloop 1] (the generator), and [kloop k = γ^k]. *)
  Definition gamma : refl (pt B2Z) = refl (pt B2Z) := kloop (iplus 1).

  Definition kloop_pow (k : ℤ) : kloop k = loopexp gamma (toInt k).
  Proof.
    apply Psi_inj.
    refine (Psi_kloop k @ _ @ (ap_loopexp _ gamma (toInt k))^).
    exact (ap (fun p => loopexp p (toInt k))
             (Psi_kloop (iplus 1) @ loopexp_succ_r loop zero @ concat_1p loop))^.
  Defined.

  (** Integer powers in the library's sense agree with [ppow] on [ℕ]. *)
  Definition loopexp_ppow {X : Type} {x : X} (p : x = x) (n : nat)
    : loopexp p (toInt (iplus n)) = ppow p n.
  Proof.
    induction n as [|n IH].
    - exact refl.
    - exact (ap (loopexp p) (toInt_zs (iplus n)) @ loopexp_succ_r p _
             @ (trans_is_concat _ _)^ @ ap (fun u => p ⋅ u) IH).
  Defined.

  (** Write [F_k(z,w) :≡ m_k(z)(w)], with the sides of its square at
      [(loop,loop)] identified with [refl] by [eP_k], [eQ_k]. *)
  Definition F_k (k : ℤ) : S1 -> S1 -> utype B2Z := fun z w => fst (fst (m_k k) z) w.
  Definition eP_k (k : ℤ) := eP_of B2Z (ell_k k).
  Definition eQ_k (k : ℤ) := eQ_of B2Z (ell_k k).

  (** The w-outer reading of [m_k] is [kγ], with [γ] that of [m_1]. *)
  Definition reading_m_1 : loops_reading (F_k (iplus 1)) loop loop (eP_k _) (eQ_k _) = gamma
    := reading_m_k (iplus 1).

  Definition reading_m_k_gamma (k : ℤ)
    : loops_reading (F_k k) loop loop (eP_k k) (eQ_k k) = loopexp gamma (toInt k)
    := reading_m_k k @ kloop_pow k.

  (** [TBD1], for [k : ℕ]: precomposing [m_1] with the degree [k] map in
      either argument gives the same 2-loop as [m_k]. *)
  Definition reading_m_1_dg1 (n : nat)
    : loops_reading (fun z w => F_k (iplus 1) (dg n z) w) loop loop
        (eP_dg1 (F_k (iplus 1)) (eP_k _) n) (eQ_k _)
      = loops_reading (F_k (iplus n)) loop loop (eP_k _) (eQ_k _)
    := loops_reading_dg1 _ _ _ n @ ap (fun g => ppow g n) reading_m_1
       @ (reading_m_k_gamma (iplus n) @ loopexp_ppow gamma n)^.

  Definition reading_m_1_dg2 (n : nat)
    : loops_reading (fun z w => F_k (iplus 1) z (dg n w)) loop loop
        (eP_k _) (eQ_dg2 (F_k (iplus 1)) (eQ_k _) n)
      = loops_reading (F_k (iplus n)) loop loop (eP_k _) (eQ_k _)
    := loops_reading_dg2 _ _ _ n @ ap (fun g => ppow g n) reading_m_1
       @ (reading_m_k_gamma (iplus n) @ loopexp_ppow gamma n)^.

  (** By [loops_reading_indep] the choice of [eP_k], [eQ_k] does not
      matter. *)
  Definition reading_m_k_any (k : ℤ)
    (eP : refl = ap (fun z => F_k k z base) loop) (eQ : refl = ap (F_k k base) loop)
    : loops_reading (F_k k) loop loop eP eQ = loopexp gamma (toInt k)
    := loops_reading_indep _ _ _ _ _ _ _ @ reading_m_k_gamma k.

  (** [TBD1] for all [k : ℤ]: precomposing [m_1] with the degree [k]
      map ([dgZ]) in either argument gives the 2-loop of [m_k], for any
      identifications of the sides with [refl]. *)
  Definition reading_m_1_dgZ1 (k : ℤ)
    (eP' : refl = ap (fun z => F_k (iplus 1) (dgZ k z) base) loop)
    (eQ' : refl = ap (F_k (iplus 1) base) loop)
    (eP : refl = ap (fun z => F_k k z base) loop) (eQ : refl = ap (F_k k base) loop)
    : loops_reading (fun z w => F_k (iplus 1) (dgZ k z) w) loop loop eP' eQ'
      = loops_reading (F_k k) loop loop eP eQ
    := loops_reading_indep (fun z w => F_k (iplus 1) (dgZ k z) w) loop loop
         eP' eP' eQ' (eQ_k _)
       @ loops_reading_dgZ1 _ (eP_k _) (eQ_k _) k eP'
       @ ap (fun g => loopexp g (toInt k)) reading_m_1
       @ (reading_m_k_any k eP eQ)^.

  Definition reading_m_1_dgZ2 (k : ℤ)
    (eP' : refl = ap (fun z => F_k (iplus 1) z base) loop)
    (eQ' : refl = ap (fun w => F_k (iplus 1) base (dgZ k w)) loop)
    (eP : refl = ap (fun z => F_k k z base) loop) (eQ : refl = ap (F_k k base) loop)
    : loops_reading (fun z w => F_k (iplus 1) z (dgZ k w)) loop loop eP' eQ'
      = loops_reading (F_k k) loop loop eP eQ
    := loops_reading_indep (fun z w => F_k (iplus 1) z (dgZ k w)) loop loop
         eP' (eP_k _) eQ' eQ'
       @ loops_reading_dgZ2 _ (eP_k _) (eQ_k _) k eQ'
       @ ap (fun g => loopexp g (toInt k)) reading_m_1
       @ (reading_m_k_any k eP eQ)^.

  (** *** The direct equivalence [M ≃ Σ_{h : S¹ × S¹ → S¹} (id = h(base,-))]

      [ΩB²ℤ] is the component of [refl] in [S¹ = S¹], which by univalence
      is the component of [id] in [S¹ → S¹]: the map [j] below is an
      embedding with that image.  Since [S¹] is connected, postcomposing
      with [j] is an equivalence [(S¹ →* ΩB²ℤ) ≃ (S¹ →* (S¹ → S¹, id))];
      we show this via [evp], which turns postcomposition into [ap_j]. *)
  Definition jmap (r : pt B2Z = pt B2Z) : S1 -> S1 := transport idmap (ap pr1 r).

  Definition IdS1 : Ustar := ((S1 -> S1); (fun x => x)).

  (** Postcomposition with [j] (pointed by [ap_j]). *)
  Definition post (g : S1star →* loops B2Z) : S1star →* IdS1
    := ((fun z => jmap (fst g z)); ap jmap (snd g)).

  Local Definition ap4 {A1 A2 A3 A4 A5 : Type} (h1 : A1 -> A2) (h2 : A2 -> A3)
    (h3 : A3 -> A4) (h4 : A4 -> A5) {a a' : A1} (x : a = a')
    : ap (fun r => h4 (h3 (h2 (h1 r)))) x = ap h4 (ap h3 (ap h2 (ap h1 x))).
  Proof. destruct x. exact refl. Defined.

  (** [ap_j] on 2-loops is [ua0_step ∘ sigma_step]. *)
  Definition ap_jmap_eq (x : refl (pt B2Z) = refl (pt B2Z))
    : ap jmap x = fst ua0_step (fst sigma_step x).
  Proof.
    change (ap jmap x = ap (@equiv_fun S1 S1) (ap (equiv_path S1 S1)
              ((equiv_path_sigma_hprop
                (P := fun p : S1 = S1 => transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr refl)
                (refl; refl) (refl; refl))^-1
                 (ap (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 x)))).
    refine (ap4 (equiv_path_sigma _ (pt B2Z) (pt B2Z))^-1 pr1 (equiv_path S1 S1)
              (@equiv_fun S1 S1) x @ _).
    apply (ap (ap (@equiv_fun S1 S1))). apply (ap (ap (equiv_path S1 S1))).
    exact (inv_path_sigma_hprop_pr1 _ _ _)^.
  Defined.

  Definition ap_jmap_isEquiv
    : isEquiv (fun x : refl (pt B2Z) = refl (pt B2Z) => ap jmap x).
  Proof.
    refine (isEquiv_homotopic (fst (Eqv_comp sigma_step ua0_step)) _ _
              (snd (Eqv_comp sigma_step ua0_step))).
    intro x. exact (ap_jmap_eq x)^.
  Defined.

  Local Definition ap_conj {X Y : Type} (f : X -> Y) {a x : X} (u : a = x) (l : x = x)
    : (ap f u)⁻¹ ⋅ (ap f l ⋅ ap f u) = ap f (u⁻¹ ⋅ (l ⋅ u)).
  Proof. destruct u. exact (ap (ap f) (trans_1p l)⁻¹ ⋅ trans_1p (ap f l)). Defined.

  Definition evp_post (g : S1star →* loops B2Z)
    : evp _ (post g) = ap jmap (evp _ g).
  Proof.
    destruct g as [h e].
    refine (_ ⋅ ap (fun l => (ap jmap e)⁻¹ ⋅ (l ⋅ ap jmap e))
                   (ap_compose h jmap loop)).
    exact (ap_conj jmap e (ap h loop)).
  Defined.

  Definition post_isEquiv : isEquiv post.
  Proof.
    pose (ev1 := IsEquiv_of_isEquiv (evp_isEquiv (pt IdS1))).
    pose (ev0 := IsEquiv_of_isEquiv (evp_isEquiv (refl (pt B2Z)))).
    pose (aj := IsEquiv_of_isEquiv ap_jmap_isEquiv).
    assert (c : IsEquiv (fun g => evp (pt IdS1) (post g))).
    { refine (isequiv_homotopic (fun g => ap jmap (evp _ g)) _).
      intro g. exact (evp_post g)^. }
    exact (isEquiv_of_IsEquiv _ (H := @cancelL_isequiv _ _ _ (evp (pt IdS1)) post ev1 c)).
  Defined.

  Definition post_eqv : (S1star →* loops B2Z) ≃ (S1star →* IdS1) := (post; post_isEquiv).

  (** Uncurrying. *)
  Definition uncurry_eqv
    : (S1star →* IdS1) ≃ {h : S1 * S1 -> S1 & (fun x => x) = (fun w => h (base, w))}.
  Proof.
    apply Eqv_of_Equiv.
    exact (equiv_functor_sigma' (equiv_uncurry S1 S1 S1) (fun g => equiv_idmap _)).
  Defined.

  Definition M_eqv_mult
    : M ≃ {h : S1 * S1 -> S1 & (fun x => x) = (fun w => h (base, w))}
    := Eqv_comp M_eqv_loops (Eqv_comp loops_cst_eqv (Eqv_comp post_eqv uncurry_eqv)).

  (** The image of [m_k]: [h_k(z,-)] goes once around [id_S¹] along the
      [k]-loop [x ↦ ex(x)(loop^k)] as [z] goes around [loop]; for [k = 1]
      this is the multiplication of [S¹]. *)
  Definition h_k (k : ℤ) : S1 -> S1 -> S1
    := S1_rec (S1 -> S1) (fun x => x) (path_forall _ _ (kloop_pw k)).

  Definition ap_jmap_kloop (k : ℤ) : ap jmap (kloop k) = path_forall _ _ (kloop_pw k).
  Proof.
    refine (ap_jmap_eq _ @ _).
    refine (ap (fst ua0_step) (eqinv_r (snd sigma_step) _) @ _).
    refine ((eta_path_forall _ _ _)^ @ _).
    exact (ap (path_forall _ _) (eqinv_r (snd ua_step) (kloop_pw k))).
  Defined.

  Definition jmap_S1_rec (k : ℤ)
    : (fun z => jmap (S1_rec _ refl (kloop k) z)) = h_k k.
  Proof.
    refine (S1_fun_path (f := fun z => jmap (S1_rec _ refl (kloop k) z)) (g := h_k k) refl _).
    refine ((ap_compose _ jmap loop) @ ap (ap jmap) (S1_rec_loop _ refl (kloop k)) @ _).
    refine (ap_jmap_kloop k @ _).
    exact ((S1_rec_loop _ _ _)^ @ (trans_1p _)^).
  Defined.

  Definition M_eqv_mult_m (k : ℤ)
    : fst (fst M_eqv_mult (m_k k)) = uncurry (h_k k).
  Proof.
    change (fst (fst uncurry_eqv (post (fst loops_cst_eqv
              (evp _ (evp_inv _ (eqinv (snd loops_cst_eqv) (dg_k' k))))))) = uncurry (h_k k)).
    refine (ap (fun l => fst (fst uncurry_eqv (post (fst loops_cst_eqv l))))
              (evp_evp_inv _ _) @ _).
    refine (ap (fun d => fst (fst uncurry_eqv (post d))) (eqinv_r (snd loops_cst_eqv) _) @ _).
    exact (ap uncurry (jmap_S1_rec k)).
  Defined.


  (** [TBD1] in the Σ-type: [h_k(w,u) = h_1(w^k,u)], with [w^k :≡ dg_k(w)]
      ([dgZ]).  Both have [h(base,-) ≡ id], so both are elements
      [(h, refl)] of [Σ_{h : S¹ × S¹ → S¹} (id = h(base,-))], and they are
      identified there ([h_k_sigma]).  On [loop]: [ap_{h_1 ∘ dg_k}(loop)
      = (ap_{h_1}(loop))^k] ([ap_loopexp]), which is [funext] of the
      [k]-loop by [ap_jmap_kloop] and [kloop k = γ^k] ([kloop_pow]). *)
  Definition h_dg (k : ℤ) : S1 -> S1 -> S1 := fun w u => h_k (iplus 1) (dgZ k w) u.

  Definition h_k_loop (k : ℤ)
    : path_forall _ _ (kloop_pw k) = ap (h_dg k) loop.
  Proof.
    refine ((ap_jmap_kloop k)^ @ ap (ap jmap) (kloop_pow k) @ ap_loopexp jmap gamma (toInt k) @ _).
    refine (ap (fun r => loopexp r (toInt k)) (ap_jmap_kloop (iplus 1)) @ _).
    refine (ap (fun r => loopexp r (toInt k)) (S1_rec_loop _ _ _)^ @ _).
    refine ((ap_loopexp (h_k (iplus 1)) loop (toInt k))^ @ _).
    refine (ap (ap (h_k (iplus 1))) (S1_rec_loop S1 base (loopZ k))^ @ _).
    exact (ap_compose (dgZ k) (h_k (iplus 1)) loop)^.
  Defined.

  Definition h_k_dg (k : ℤ) : h_k k = h_dg k
    := S1_fun_path (f := h_k k) (g := h_dg k) refl
         (S1_rec_loop _ _ _ @ h_k_loop k @ (trans_1p _)^).

  (** An identification made by [S1_fun_path] with [p] at [base] is [p]
      at [base]. *)
  Definition S1_fun_path_base {A : Type} {f g : S1 -> A} (p : f base = g base)
    (q : ap f loop = p⁻¹ ⋅ (ap g loop ⋅ p))
    : ap (fun F => F base) (S1_fun_path p q) = p.
  Proof.
    refine ((apD10_ap_ev _ base)^ @ _).
    exact (ptw (eqinv_r (funext f g) _) base).
  Defined.

  Definition h_k_dg_base (k : ℤ) : ap (fun f => f base) (h_k_dg k) = refl
    := S1_fun_path_base _ _.

  (** Identifications in [Σ_{h : S¹ × S¹ → S¹} (id = h(base,-))] from
      identifications of the curried maps. *)
  Definition sigma_uncurry_path {f g : S1 -> S1 -> S1} (e : f = g)
    (r : (fun x => x) = f base) (r' : (fun x => x) = g base)
    (q : r' = r @ ap (fun F => F base) e)
    : ((uncurry f; r) : {h : S1 * S1 -> S1 & (fun x => x) = (fun w => h (base, w))})
      = (uncurry g; r').
  Proof. destruct e. exact (ap (fun s => (uncurry f; s)) (q @ concat_p1 r)^). Defined.

  Definition h_k_sigma (k : ℤ)
    : ((uncurry (h_k k); refl) : {h : S1 * S1 -> S1 & (fun x => x) = (fun w => h (base, w))})
      = (uncurry (h_dg k); refl)
    := sigma_uncurry_path (h_k_dg k) refl refl (concat_1p _ @ h_k_dg_base k)^.

  (** [M_eqv_mult] sends [m_k] to [(h_k, refl)], with both components. *)
  Definition jmap_S1_rec_base (k : ℤ) : ap (fun f => f base) (jmap_S1_rec k) = refl
    := S1_fun_path_base _ _.

  Definition M_eqv_mult_m_sigma (k : ℤ)
    : fst M_eqv_mult (m_k k) = (uncurry (h_k k); refl).
  Proof.
    change (fst uncurry_eqv (post (fst loops_cst_eqv
              (evp _ (evp_inv _ (eqinv (snd loops_cst_eqv) (dg_k' k))))))
            = (uncurry (h_k k); refl)).
    refine (ap (fun l => fst uncurry_eqv (post (fst loops_cst_eqv l)))
              (evp_evp_inv _ _) @ _).
    refine (ap (fun d => fst uncurry_eqv (post d)) (eqinv_r (snd loops_cst_eqv) _) @ _).
    exact (sigma_uncurry_path (jmap_S1_rec k) refl refl (concat_1p _ @ jmap_S1_rec_base k)^).
  Defined.


  (** *** [TBD2] in [M]: [swap(m_k) = m_{-k}]

      [swapM] is the map [swap] of [con:swap-ptd-doms] for [M], defined
      directly (none of the properties claimed in that construction are
      used): [swap(m)(w) :≡ (z ↦ m(z)(w))], pointed by [m'_pt(w)] (with
      [m'_pt :≡ ptw(fst(m_pt))]), and [swap(m)] pointed by the
      identification [c = swap(m)(base)] whose function part is
      [funext(z ↦ m(z)_pt)].  By definition the underlying function of
      two variables of [swap(m)] is [swap2] of that of [m]. *)
  Local Definition trp_ptb {f g : S1 -> utype B2Z} (φ : f = g) (u : pt B2Z = f base)
    : transport (fun f : S1 -> utype B2Z => pt B2Z = f base) φ u = apD10 φ base ⋅ u.
  Proof. destruct φ. exact refl. Defined.

  Local Definition pt_coh (y : utype (pmap_ptd S1star B2Z)) (e : pt (pmap_ptd S1star B2Z) = y)
    : snd y = apD10 (ap fst e) base.
  Proof. destruct e. exact refl. Defined.

  Definition swap_inner (m : M) (w : S1) : utype (pmap_ptd S1star B2Z)
    := (fun z => fst (fst m z) w; apD10 (ap fst (snd m)) w).

  Definition swapM (m : M) : M.
  Proof.
    refine (swap_inner m; _).
    refine (path_sigma' (fun f : S1 -> utype B2Z => pt B2Z = f base)
              (path_forall (fun _ => pt B2Z) (fun z => fst (fst m z) base) (fun z => snd (fst m z))) _).
    refine (trp_ptb (f := fun _ => pt B2Z) (g := fun z => fst (fst m z) base) _ (refl (pt B2Z)) @ _).
    refine (trans_1p _ @ _).
    exact (apD10_path_forall (fun _ => pt B2Z) (fun z => fst (fst m z) base)
             (fun z => snd (fst m z)) base @ pt_coh (fst m base) (snd m)).
  Defined.

  Definition swapM_fun (m : M)
    : (fun z w => fst (fst (swapM m) z) w) = swap2 (fun z w => fst (fst m z) w)
    := refl.

  (** Readings along an identification of functions of two variables are
      transported along its value at the base points. *)
  Definition loops_reading_trp {A B C : Type} {F F' : A -> B -> C} (ρ : F = F')
    {a : A} {b : B} (p : a = a) (q : b = b)
    (eP : refl = ap (fun z => F z b) p) (eQ : refl = ap (F a) q)
    (eP' : refl = ap (fun z => F' z b) p) (eQ' : refl = ap (F' a) q)
    : loops_reading F' p q eP' eQ'
      = transport (fun c => refl c = refl c) (ap (fun G => G a b) ρ) (loops_reading F p q eP eQ).
  Proof. destruct ρ. exact (loops_reading_indep _ _ _ _ _ _ _). Defined.

  (** [B²ℤ] is simply connected: every loop at [pt] is merely [refl]. *)
  Local Definition trp_Tr_refl {X : Type} (p : S1 = X)
    : transport (fun X => Tr 0 (S1 = X)) p (tr refl) = tr p.
  Proof. destruct p. exact refl. Defined.

  Definition B2Z_loop_merely_refl (δ : pt B2Z = pt B2Z) : Tr (-1) (δ = refl).
  Proof.
    pose (s := (trp_Tr_refl δ..1)^ @ δ..2 : tr δ..1 = tr refl :> Tr 0 (S1 = S1)).
    refine (Trunc_functor (-1) _ ((equiv_path_Tr _ _)^-1 s)). intro r.
    refine ((eta_path_sigma δ)^ @ _).
    revert r. generalize (δ..2). generalize (δ..1). intros p q r.
    pose (r' := r^). clearbody r'. clear r. revert q. destruct r'. intro q.
    refine (ap (path_sigma _ (pt B2Z) (pt B2Z) refl) (y := refl) _).
    apply path_ishprop.
  Defined.

  Definition omega2_trp (δ : pt B2Z = pt B2Z) (x : refl (pt B2Z) = refl (pt B2Z))
    : fst omega2_B2Z_eqv (transport (fun c => refl c = refl c) δ x) = fst omega2_B2Z_eqv x.
  Proof.
    refine (@Trunc_rec (-1) _ _ (isSet_IsHSet ℤ_isSet _ _) _ (B2Z_loop_merely_refl δ)).
    intro r. exact (ap (fun d => fst omega2_B2Z_eqv (transport (fun c => refl c = refl c) d x)) r).
  Defined.

  (** Integer powers of an inverse. *)
  Local Definition loopexp_neg_succ {X : Type} {x : X} (p : x = x) (y : Int)
    (IH : loopexp p (int_neg y) = (loopexp p y)^)
    : loopexp p (int_neg (int_succ y)) = (loopexp p (int_succ y))^
    := ap (loopexp p) (int_neg_succ y) @ loopexp_pred_r p _ @ ap (fun r => r @ p^) IH
       @ (inv_pp p _)^ @ ap inverse (loopexp_succ_l p y)^.

  Local Definition loopexp_neg_pred {X : Type} {x : X} (p : x = x) (y : Int)
    (IH : loopexp p (int_neg y) = (loopexp p y)^)
    : loopexp p (int_neg (int_pred y)) = (loopexp p (int_pred y))^
    := ap (loopexp p) (int_neg_pred y) @ loopexp_succ_r p _ @ ap (fun r => r @ p) IH
       @ ap (fun r => _ @ r) (inv_V p)^ @ (inv_pp p^ _)^ @ ap inverse (loopexp_pred_l p y)^.

  Definition loopexp_neg {X : Type} {x : X} (p : x = x) (z : Int)
    : loopexp p (int_neg z) = (loopexp p z)^.
  Proof.
    induction z as [|z IH|z IH] using Int_ind.
    - exact refl.
    - exact (loopexp_neg_succ p _ IH).
    - exact (loopexp_neg_pred p _ IH).
  Defined.

  Definition kloop_neg (k : ℤ) : kloop (zneg k) = (kloop k)^.
  Proof.
    apply Psi_inj.
    refine (Psi_kloop _ @ _ @ (ap_V _ (kloop k))^).
    refine (ap (loopexp loop) (toInt_zneg k) @ loopexp_neg loop (toInt k) @ _).
    exact (ap inverse (Psi_kloop k))^.
  Defined.

  (** [M_eqv_Z(swap(m_k)) = -k]: [M_eqv_Z] reads off the w-outer
      reading ([reading_lc], after the identification
      [swap(m_k) = evp⁻¹(evp(swap(m_k)))]); the w-outer reading of
      [swap(m_k)] is that of [swap2(F_k)], which is the inverse of that of
      [F_k] ([loops_reading_swap]), i.e. of [kloop k] ([reading_m_k]). *)
  Definition M_eqv_Z_swap (k : ℤ) : fst M_eqv_Z (swapM (m_k k)) = zneg k.
  Proof.
    pose (l' := evp _ (swapM (m_k k))).
    pose (ρ := ap (fun X : M => fun z w => fst (fst X z) w) (evp_inv_evp _ (swapM (m_k k)))^
               : swap2 (F_k k) = F_of B2Z l').
    change (fst omega2_B2Z_eqv (evp _ (fst (lc_eqv B2Z) l')) = zneg k).
    refine (ap (fst omega2_B2Z_eqv) (reading_lc B2Z l')^ @ _).
    refine (ap (fst omega2_B2Z_eqv)
              (loops_reading_trp ρ loop loop (eQ_k k) (eP_k k) (eP_of B2Z l') (eQ_of B2Z l')) @ _).
    refine (omega2_trp _ _ @ _).
    refine (ap (fst omega2_B2Z_eqv) (loops_reading_swap (F_k k) loop loop (eP_k k) (eQ_k k)) @ _).
    refine (ap (fun x => fst omega2_B2Z_eqv x^) (reading_m_k k) @ _).
    exact (ap (fst omega2_B2Z_eqv) (kloop_neg k)^ @ omega2_kloop (zneg k)).
  Defined.

  (** [TBD2]: [swap(m_k) = m_{-k}] in [M], since [M_eqv_Z] is an
      equivalence. *)
  Definition swap_m_k (k : ℤ) : swapM (m_k k) = m_k (zneg k)
    := (eqinv_l (snd M_eqv_Z) _)^
       @ ap (eqinv (snd M_eqv_Z)) (M_eqv_Z_swap k @ (M_eqv_Z_m (zneg k))^)
       @ eqinv_l (snd M_eqv_Z) _.

End MEqvZ.
