import CyclotomicNT

/-!
Axiom audit: flt-cyclotomic-nt: Stickelberger annihilation, Herbrand, Kummer Case I, [E:C] = h+, analytic foundations
Run with:  lake env lean AxiomAudit.lean
Expected axiom base: [propext, Classical.choice, Quot.sound]
-/

#print axioms CyclotomicNT.stickelberger_annihilates
#print axioms stickelberger_annihilates_ideal
#print axioms CyclotomicNT.herbrand
#print axioms CyclotomicNT.caseI_of_not_irregular
#print axioms CyclotomicNT.cyclotomic_unit_index
#print axioms dedekindZeta_eulerProduct
#print axioms CyclotomicNT.DedekindFactorization.prod_dirichletL_eq_tprod
#print axioms CyclotomicNT.circulant_mulVec_addChar
#print axioms CyclotomicNT.circulant_mul_charMatrix
#print axioms CyclotomicNT.det_charMatrix_ne_zero
#print axioms DirichletCharacter.generalizedBernoulli
#print axioms CyclotomicNT.LFunction_zero_odd
#print axioms CyclotomicNT.gaussSum_mul_LFunction_one_even
#print axioms CyclotomicNT.QiCert.bern_eq
