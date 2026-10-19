-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GFrame.Labels.Maps
import Submission.Work.GFrame.Labels.Conj
import Submission.Work.GFrame.Labels.GCarrier
import Submission.Work.GFrame.Labels.Proj
import Submission.Work.GFrame.Labels.ConjB
import Submission.Work.GFrame.Labels.StageBSem
import Submission.Work.GFrame.Labels.SchedR
import Submission.Work.GFrame.Labels.GeomOld

/-!
# GFrame labels (key: eng-labels): everything together

One import for the integrator; checks that all label modules (and the ENGINE and CLIFFORD
modules they use) load together without a name clash, and prints the axioms of the main
theorems.  No `sorry`.
-/

#print axioms OAI.PowerSaving.GF.gsched_route
#print axioms OAI.PowerSaving.GF.gsched_groute
#print axioms OAI.PowerSaving.GF.gsched_groute_R
#print axioms OAI.PowerSaving.GF.sched_route_any
#print axioms OAI.PowerSaving.GF.GXMap.toXMap
#print axioms OAI.PowerSaving.GF.altAt_gcalc
#print axioms OAI.PowerSaving.GF.asched_groute
#print axioms OAI.PowerSaving.GF.bsched_groute_full
#print axioms OAI.PowerSaving.GF.hsched_groute
#print axioms OAI.PowerSaving.GF.SMv.of_sub
#print axioms OAI.PowerSaving.GF.SMv.of_sup
#print axioms OAI.PowerSaving.GF.fmv_old_to_core
#print axioms OAI.PowerSaving.GF.BXMap.fmv_sub
#print axioms OAI.PowerSaving.GF.SLbl.rep_eq_iff
#print axioms OAI.PowerSaving.GF.gxmap1
#print axioms OAI.PowerSaving.GF.gxmap2
#print axioms OAI.PowerSaving.GF.gxmapQ
#print axioms OAI.PowerSaving.GF.gxmapB
#print axioms OAI.PowerSaving.GF.gxmapB_toXMap
#print axioms OAI.PowerSaving.GF.BXMap.ofConj
#print axioms OAI.PowerSaving.GF.GCarrier.fwd_route
#print axioms OAI.PowerSaving.GF.GCarrier.bwd_route
#print axioms OAI.PowerSaving.GF.Carrier.toG
#print axioms OAI.PowerSaving.GF.complete_proj
