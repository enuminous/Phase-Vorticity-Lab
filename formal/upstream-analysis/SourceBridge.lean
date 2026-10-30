import Madelung
import Vorticity
import RotationKinematics
import RotatingCosmology

/-!
PVL-001 source probe. No new axioms or new physical theorems.
This probe was prepared from inspected declarations but has NOT been run locally.
The original 1+1D/Cartesian hypotheses and scopes are retained by #check.
-/

#check MonolithicAnalysis.Polar.norm_sq
#check MonolithicAnalysis.Madelung.current_eq_im_conj_wave_deriv
#check MonolithicAnalysis.Madelung.kleinGordon_implies_current_conservation
#check MonolithicAnalysis.Madelung.schrodinger_iff_madelung
#check MonolithicAnalysis.Madelung.schrodinger_factorization
#check MonolithicAnalysis.Vorticity.curl_gradient
#check MonolithicAnalysis.Vorticity.curl_smul
#check MonolithicAnalysis.Vorticity.rigid_rotation_curl
#check MonolithicAnalysis.RotationKinematics.angular_field_curl
#check MonolithicAnalysis.RotatingCosmology.vector_rate_from_curl

#print axioms MonolithicAnalysis.Polar.norm_sq
#print axioms MonolithicAnalysis.Madelung.current_eq_im_conj_wave_deriv
#print axioms MonolithicAnalysis.Madelung.kleinGordon_implies_current_conservation
#print axioms MonolithicAnalysis.Madelung.schrodinger_iff_madelung
#print axioms MonolithicAnalysis.Madelung.schrodinger_factorization
#print axioms MonolithicAnalysis.Vorticity.curl_gradient
#print axioms MonolithicAnalysis.Vorticity.curl_smul
#print axioms MonolithicAnalysis.Vorticity.rigid_rotation_curl
#print axioms MonolithicAnalysis.RotationKinematics.angular_field_curl
#print axioms MonolithicAnalysis.RotatingCosmology.vector_rate_from_curl
