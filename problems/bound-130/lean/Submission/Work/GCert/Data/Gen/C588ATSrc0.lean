-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.SourceReplayDef
import Submission.Work.GCert.Data.Gen.C588AT
/-! Finite structural facts for the C588AT source adapter (not `GS.scalCheck`).
`sourceCheck` of a full packed batch is deferred: `decide +kernel` of
`segCheck … (sourceProg raw)` does not reduce in the kernel (VM appears to
accept n=1; kernel type-mismatch).  These facts are kernel-small. -/
set_option maxRecDepth 100000
namespace GXD.C588AT
open GXD
/-- the 28 phase-A x→x shears (tgt, src), first witness A181 = (0, 27) -/
def xxShears : List (Nat × Nat) :=
  [(0, 27), (27, 0), (70, 91), (91, 70), (72, 89), (89, 72), (12, 31), (31, 12),
   (101, 55), (55, 101), (98, 85), (85, 98), (49, 33), (33, 49), (6, 1), (1, 6),
   (83, 74), (74, 83), (80, 88), (88, 80), (68, 4), (4, 68), (15, 53), (53, 15),
   (13, 51), (51, 13), (36, 111), (111, 36)]

/-- `okBK` accepts every actual phase-A x→x shear (`nr = 2v+R = 812`) -/
theorem xxShears_okB :
    xxShears.all (fun p => GS.okBK 112 224 812 p.1 p.2) = true := by decide +kernel

/-- unchanged `okAK` rejects every actual phase-A x→x shear -/
theorem xxShears_notA :
    xxShears.all (fun p => ! GS.okAK 112 224 812 p.1 p.2) = true := by decide +kernel

/-- Phase A never reads a y role. -/
theorem aNoY_ok : GS.aNoYK raw = true := by decide +kernel

/-- Phase A never writes a y role. -/
theorem aNoYtgt_ok : GS.aNoYtgtK raw = true := by decide +kernel

/-- `sourceProg` is the A-chunks as `cB`, scatter, B-chunks. -/
theorem sourceProg_len :
    (GS.sourceProg raw).length = raw.A.length + raw.B.length + 1 := by decide +kernel

end GXD.C588AT
#print axioms GXD.C588AT.xxShears_okB
#print axioms GXD.C588AT.xxShears_notA
#print axioms GXD.C588AT.aNoY_ok
#print axioms GXD.C588AT.aNoYtgt_ok
#print axioms GXD.C588AT.sourceProg_len
