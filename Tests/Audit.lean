import PlonkLean.KZG.TranscriptSecurity
import PlonkLean.KZG.Soundness
import PlonkLean.Crypto.QSDHProbability

/-! # Headline-theorem trust audit

`#print axioms` is intentionally part of the default test target.  CI therefore
prints the transitive logical assumptions of the security-critical theorems on
every build instead of leaving the trust surface hidden in documentation.
-/

#print axioms PlonkLean.KZG.kzg_AGM_soundness_or_rootCollision
#print axioms PlonkLean.KZG.schwartzZippel_univariate
#print axioms PlonkLean.KZG.quotientIdentity_bad_alpha_count
#print axioms PlonkLean.KZG.quotientCheck_bad_alpha_zeta_count
#print axioms PlonkLean.KZG.unsatisfied_of_copyConstraints_bad_alpha_zeta_count
#print axioms PlonkLean.KZG.permutationBadBetaGammaPairs_card_le
#print axioms PlonkLean.KZG.unsatisfied_bad_four_challenge_count
#print axioms PlonkLean.Probability.unsatisfied_plonk_uniform_false_acceptance_probability_le_one_div
#print axioms PlonkLean.Probability.unsatisfied_fourQueryFiatShamir_false_acceptance_probability_le_one_div
#print axioms PlonkLean.Crypto.bytePlonkQuerySet_card
#print axioms PlonkLean.Crypto.unsatisfied_bytePlonkPCS_false_acceptance_probability_le
#print axioms PlonkLean.KZG.decodePlonkKZGOpeningPacket_encode
#print axioms PlonkLean.KZG.parsedPlonkKZGByteVerifier_extractionSound
#print axioms PlonkLean.KZG.unsatisfied_parsedPlonkKZGByteVerifier_probability_le
#print axioms PlonkLean.KZG.decodePlonkKZGWitnessCommitments_encode
#print axioms PlonkLean.KZG.fullyParsedPlonkKZGByteVerifier_extractionSound_of_qsdh
#print axioms PlonkLean.KZG.unsatisfied_fullyParsedPlonkKZG_probability_le_of_qsdh
#print axioms PlonkLean.Crypto.QSDHMachine.tauHardness_of_hardWithin
#print axioms PlonkLean.KZG.unsatisfied_fullyParsedPlonkKZG_probability_le_of_bounded_qsdh
#print axioms PlonkLean.Crypto.randomizedRootCollisionAdvantage_le_of_qsdhSecure
#print axioms PlonkLean.Crypto.kzg_soundness_of_qsdhHard
