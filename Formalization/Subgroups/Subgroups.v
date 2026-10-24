(** * Chapter 9 of [subgroups.tex]: Normal subgroups and quotients

    ** Summary of this formalization

    Section 9.1 is an overview without results.  Sections 9.2 - 9.8:
    epimorphisms and monomorphisms ([S02_Epis.v]), images, kernels and
    cokernels ([S03_Images.v]), the action on the set of subgroups
    ([S04_SubgroupAction.v]), normal subgroups ([S05_Normal.v]),
    intersecting with normal subgroups ([S06_IntersectNormal.v]),
    automorphisms of groups ([S07_Automorphisms.v]) and the Weyl group
    ([S08_Weyl.v]), one file per section, each starting with its own
    summary.  They build on Chapters 2 - 8 ([ConGroups.ConGroups]).
    Everything compiles with nothing admitted.

    Main results: monomorphisms of groups are the injections on
    symmetries and the coverings ([lem:eq-mono-cover]); surjections on
    symmetries are epimorphisms and have connected fibers; kernels,
    cokernels and images, with the image factorization into an
    epimorphism and a monomorphism.  The converse [epi ⇒ surjective] is
    stated only, since the book's proof depends on the draft
    construction [con:monos-are-equalizers]; many results of 9.5 depend
    on it and are stated only.  [Mono(G)], [Sub(G)] and quotient groups
    run into size issues, documented in the section files. *)

From SymmetryBook Require Export
  Subgroups.S02_Epis
  Subgroups.S03_Images
  Subgroups.S04_SubgroupAction
  Subgroups.S05_Normal
  Subgroups.S06_IntersectNormal
  Subgroups.S07_Automorphisms
  Subgroups.S08_Weyl.
