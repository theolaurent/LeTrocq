/-
The LeTrocq STANDARD LIBRARY: `Prod` (×, the cartesian product).

`List` with TWO type parameters instead of one — and non-dependent (unlike `Sigma`, whose second component
lives over the first). `ProdR` is the parametricity relation (a TYPE FORMER over both parameters: the
translation crosses `A × B` by feeding each parameter's `(_, _, _)` triple in turn), `ProdMkR` the
constructor TERM primitive, `paramProdR` the `(4,4)` relator (two independent `Param` arguments).
-/
import LeTrocq.Attr
namespace LeTrocq.ParamLib
open LeTrocq MapClass

/-- two pairs are related iff their components are componentwise related. The parameter order
    `(A, A', RA, B, B', RB)` is what the translation supplies (one `mkApp3` triple per type parameter). -/
@[trocq] inductive ProdR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type) :
    A × B → A' × B' → Type
  | mk {a a' b b'} (aR : RA a a') (bR : RB b b') : ProdR A A' RA B B' RB (a, b) (a', b')

theorem ProdR.allEq {A A' : Type} {RA : A → A' → Type} {B B' : Type} {RB : B → B' → Type}
    (hA : ∀ a a' (x y : RA a a'), x = y) (hB : ∀ b b' (x y : RB b b'), x = y)
    {p : A × B} {q : A' × B'} (x y : ProdR A A' RA B B' RB p q) : x = y := by
  cases x with | mk aR bR => cases y with | mk aR' bR' => rw [hA _ _ aR aR', hB _ _ bR bR']

/-- `Prod.mk` as a TERM primitive: the four triples are the two type parameters then the two components. -/
@[trocq] def ProdMkR (A A' : Type) (RA : A → A' → Type) (B B' : Type) (RB : B → B' → Type)
    (a : A) (a' : A') (aR : RA a a') (b : B) (b' : B') (bR : RB b b') :
    ProdR A A' RA B B' RB (a, b) (a', b') := .mk aR bR

/-- `A × B ≃ A' × B'` at the top class, from equivalences of the two components: the maps act componentwise,
    completeness `cases` the relation (which packages both component relatednesses), coherence free. -/
@[trocq] noncomputable def paramProdR (A A' : Type) (pa : Param map4 map4 A A')
    (B B' : Type) (pb : Param map4 map4 B B') :
    Param map4 map4 (A × B) (A' × B') where
  R := ProdR A A' pa.R B B' pb.R
  cov :=
    { map := fun p => (pa.cov.map p.1, pb.cov.map p.2)
      map_in_R := fun p _ h => by
        subst h; exact .mk (pa.cov.map_in_R p.1 _ rfl) (pb.cov.map_in_R p.2 _ rfl)
      R_in_map := fun _ _ r => by
        cases r with | @mk a a' b b' aR bR =>
          show (pa.cov.map a, pb.cov.map b) = (a', b')
          rw [pa.cov.R_in_map a a' aR, pb.cov.R_in_map b b' bR]
      R_in_mapK := fun _ _ _ => ProdR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
        (fun b b' => (pb.cov.subsingleton b b').allEq) _ _ }
  contra :=
    { map := fun q => (pa.contra.map q.1, pb.contra.map q.2)
      map_in_R := fun q _ h => by
        subst h; exact .mk (pa.contra.map_in_R q.1 _ rfl) (pb.contra.map_in_R q.2 _ rfl)
      R_in_map := fun _ _ r => by
        cases r with | @mk a a' b b' aR bR =>
          show (pa.contra.map a', pb.contra.map b') = (a, b)
          rw [pa.contra.R_in_map a' a aR, pb.contra.R_in_map b' b bR]
      R_in_mapK := fun _ _ _ => ProdR.allEq (fun a a' => (pa.cov.subsingleton a a').allEq)
        (fun b b' => (pb.cov.subsingleton b b').allEq) _ _ }

end LeTrocq.ParamLib
