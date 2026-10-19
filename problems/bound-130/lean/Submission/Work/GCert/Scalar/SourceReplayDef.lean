-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.Seg

/-!
# Source-replay kernel terms (okBK on phase A)

Core Lean only, so `decide +kernel` can evaluate them.  A NEW item list, not `GS.prog`.
Phase-A chunks are `Item.cB`.  This is not `scalCheck`.  Soundness: `SourceReplay.lean`.
-/

namespace GS
open SSC GXD

/-- Phase A encoded with `Item.cB` (okBK), then scatter, then phase B. -/
def sourceProg (c : Raw) : List Item := c.A.map Item.cB ++ (Item.scat :: c.B.map Item.cB)

/-- Kernel check of `sourceProg` (not `scalCheck`). -/
noncomputable def sourceCheck (c : Raw) (p : SPar) (lo n : Nat) : Bool :=
  segCheck c p lo n none (sourceProg c) none

/-- Phase A never reads a y role. -/
def aNoYK (c : Raw) : Bool :=
  (c.gatesA.flatMap Gate.adds).all fun x =>
    Nat.ble (Nat.succ x.2.1) c.v || Nat.ble (2 * c.v) x.2.1

/-- Phase A never writes a y role. -/
def aNoYtgtK (c : Raw) : Bool :=
  (c.gatesA.flatMap Gate.adds).all fun x =>
    Nat.ble (Nat.succ x.1) c.v || Nat.ble (2 * c.v) x.1

end GS
