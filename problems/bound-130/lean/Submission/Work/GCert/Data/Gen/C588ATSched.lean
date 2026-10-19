-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Data.Gen.C588ATRows0
import Submission.Work.GCert.Data.Gen.C588ATRows1
import Submission.Work.GCert.Data.Gen.C588ATRows2
import Submission.Work.GCert.Data.Gen.C588ATRows3
import Submission.Work.GCert.Data.Gen.C588ATRows4
import Submission.Work.GCert.Data.Gen.C588ATRows5
import Submission.Work.GCert.Data.Gen.C588ATRows6
import Submission.Work.GCert.Data.Gen.C588ATRows7
import Submission.Work.GCert.Data.Gen.C588ATRows8
import Submission.Work.GCert.Data.Gen.C588ATRows9
import Submission.Work.GCert.Data.Gen.C588ATRows10
import Submission.Work.GCert.Data.Gen.C588ATRows11
import Submission.Work.GCert.Data.Gen.C588ATRows12
import Submission.Work.GCert.Data.Gen.C588ATRows13
import Submission.Work.GCert.Data.Gen.C588ATRows14
import Submission.Work.GCert.Data.Gen.C588ATRows15
import Submission.Work.GCert.Data.Gen.C588ATRows16
import Submission.Work.GCert.Data.Gen.C588ATRows17
import Submission.Work.Bridge401.SchedK
set_option maxRecDepth 100000
namespace GXD.C588AT
open OAI.PowerSaving
noncomputable def schedRows : List (List Nat) := bankRows0 ++ bankRows1 ++ bankRows2 ++ bankRows3 ++ bankRows4 ++ bankRows5 ++ bankRows6 ++ bankRows7 ++ bankRows8 ++ bankRows9 ++ bankRows10 ++ bankRows11 ++ bankRows12 ++ bankRows13 ++ bankRows14 ++ bankRows15 ++ bankRows16 ++ bankRows17
def schedPad : List Nat := List.replicate 4248 0 ++ List.replicate 504 1 ++ List.replicate 72 68
def schedRes : List Nat := [9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 8, 9, 8, 9, 8, 9, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 8, 9, 8, 9, 8, 8, 8, 8, 7, 7, 7, 7, 9, 9, 9, 9, 8, 8, 8, 8, 8, 9, 8, 9, 8, 9, 8, 9, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 9, 9, 8, 8, 7, 7, 7, 7, 7, 7, 7, 7, 9, 9, 8, 8, 9, 9, 9, 9, 7, 7, 7, 7, 9, 9, 8, 8, 9, 8, 9, 8, 7, 7, 7, 7, 9, 9, 8, 8, 9, 8, 9, 8, 8, 9, 8, 9, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 5, 8, 5, 5, 5, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 4, 8, 4, 4, 4, 8, 8, 8, 5, 8, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9]
theorem sched_ok : GX.schedK 4824 raw.R schedRows schedPad schedRes = true := by
  decide +kernel
theorem pad_profile : (schedPad.count 0, schedPad.count 1, schedPad.count 68) = (4248, 504, 72) := by decide +kernel
end GXD.C588AT
#print axioms GXD.C588AT.sched_ok
