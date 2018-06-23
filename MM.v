Require Import QArith.

Record Space : Type :=
  { Cover : Type
  ; rep   : Cover -> Type
  }.

Arguments rep {_} _.

Definition Point (A : Space) :=
  forall ca : Cover A, rep ca.

Definition Map (A B : Space) := Point A -> Point B.

Definition Real : Space :=
  {| Cover := Q
   ; rep := fun _ => Q
  |}.

Definition discrete (A : Type) : Space :=
  {| Cover := unit
     ; rep := fun _ => A
  |}.

Definition discrete_Pt {A : Type} (x : A) : Point (discrete A) :=
  fun _ => x.

Definition discrete_Map {A : Type} {B : Space} (f : A -> Point B)
  : Map (discrete A) B := fun x cb => f (x tt) cb.

Definition Sum (A B : Space) : Space :=
  {| Cover := Cover A * Cover B
     ; rep := fun p => (rep (fst p) + rep (snd p))%type
  |}.

Definition Inl {A B : Space} : Map A (Sum A B) :=
  fun x cab => inl (x (fst cab)).

Definition Inr {A B : Space} : Map B (Sum A B) :=
  fun x cab => inr (x (snd cab)).

Definition Pair (A B : Space) : Space :=
  {| Cover := Cover A + Cover B 
  ; rep := fun p => match p with
                 | inl ca => rep ca
                 | inr cb => rep cb
                 end |}.

Definition Rplus : Map (Pair Real Real) Real :=
  fun xy eps => let x := xy (inl (eps / inject_Z 2)) in
             let y := xy (inr (eps / inject_Z 2)) in
             x + y.

Require Import QArith.Qminmax
               QArith.Qabs.

(* This is wrong. *)
Definition Rmult : Map (Pair Real Real) Real :=
  fun xy eps => let x1 := xy (inl (inject_Z 1)) in
             let y1 := xy (inr (inject_Z 1)) in
             let lipK := Qmax (Qabs x1) (Qabs y1) + 1 in
             let eps := Qinv lipK / inject_Z 2 in 
             let x := xy (inl eps) in
             let y := xy (inr eps) in
             x * y.

Inductive Real :=
  | OpenBall : Q -> 
