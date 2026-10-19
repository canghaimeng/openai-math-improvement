-- Packaging change: local imports prefixed with Submission; mathematical declarations preserved.
import Submission.Work.GCert.Scalar.SourceReplayDef

/-!
New proof-checker packing with 16-bit checksum weights. This changes no existing
checker, certificate, scalar matrix, frame or algorithm. Generic replay guards
are unchanged. Semantic use requires separately proved initialization and
replay soundness lemmas; Boolean checks alone do not supply those lemmas.

Definitions follow the attributed GS.gInit/segCheck and gauged gInitL/eCheck
interfaces (Sussman; the #401 gauged extension), with checksum modulus65536.
-/

namespace GS.Tag16
open SSC GXD

noncomputable def init (sw u off : Nat) (n : Nat) : Nat → Trie → (Trie → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool) (fun _ t k => k t)
    (fun _ ih i t k => forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 65536))) fun b =>
      forceN (Nat.succ i) fun i2 => ih i2 (t.set (Nat.add off i) b) k) n

noncomputable def segCheck (c : Raw) (p : SPar) (lo n : Nat) (pre : Option Trie)
    (items : List Item) (post : Option Trie) : Bool :=
  gPre c p lo n fun v2 nr hi tm K m2 => forceN (List.length c.ret) fun rl =>
    Option.rec (motive := fun _ => (Trie → Bool) → Bool)
      (fun k => init p.sw p.ux lo n 0 (Trie.mk p.d) k) (fun t k => k t) pre fun tr0 =>
        gItems c p v2 nr tm K m2 rl items tr0 fun tr3 =>
          Option.rec (motive := fun _ => Bool)
            (guard (gFin p.sw K m2 p.ux 0 lo hi tr3 c.v 0)
              (gFin p.sw K m2 p.uy c.v lo hi tr3 c.v 0))
            (fun t => beqK tr3 t) post

noncomputable def sourceCheck (c : Raw) (p : SPar) (lo n : Nat) : Bool :=
  segCheck c p lo n none (sourceProg c) none

noncomputable def incK (nr : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih lo => guard (Nat.ble lo r)
      (guard (Nat.ble (Nat.succ r) nr) (ih (Nat.succ r))))

noncomputable def initL (sw u : Nat) : List Nat → Nat → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool) (fun _ t k => k t)
    (fun r _ ih i t k => forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 65536))) fun b =>
      forceN (Nat.succ i) fun i2 => ih i2 (t.set r b) k)

noncomputable def sourceECheck (c : Raw) (p : SPar) (gl : List Nat) : Bool :=
  gPre c p 0 gl.length fun v2 nr _ tm K m2 =>
    guard (incK nr gl v2) (guard (Nat.ble (Nat.succ p.us) (Nat.pow 2 (Nat.sub p.sw 1)))
      (guard (Nat.ble (Nat.succ p.us) 2147483648)
        (forceN (List.length c.ret) fun rl =>
          initL p.sw p.us gl 0 (Trie.mk p.d) fun tr0 =>
            gItems c p v2 nr tm K m2 rl (sourceProg c) tr0 fun tr3 =>
              gFin p.sw K m2 p.uy c.v 0 0 tr3 c.v 0)))

end GS.Tag16
