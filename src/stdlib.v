(* Logic.v *)

Definition Type := Type({}).
Inductive True : Prop := I : True.
Inductive False : Prop :=.

Definition not (A:Prop) := A -> False.
Definition notT (A:Type) := A -> False.

Inductive and (A B:Prop) : Prop := conj : A -> B -> and A B.
Theorem proj1 : forall A B: Prop, and A B -> A. intros. exact (match H as _ in and _ _ return A with | conj _ _ a _ => a end). Qed.
Theorem proj2 : forall A B: Prop, and A B -> B. intros. exact (match H as _ in and _ _ return B with | conj _ _ _ b => b end). Qed.

Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> or A B
  | or_intror : B -> or A B.

Definition iff (A B: Prop) := and (A -> B) (B -> A).

(* TODO: Theorems for iff *)
Inductive ex (A:Prop) (P:A -> Prop) : Prop := | ex_intro : forall x:A, P x -> ex A P.
Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : eq A x x.

Lemma eq_ind : forall (A: Set) (x y: A) (P: A -> Prop), eq A x y -> P x -> P y.
  intros. exact (match H as _ in eq _ _ a return P a with | eq_refl _ _ => H1 end).
Qed.
Theorem fun_eq : forall (A B: Set) (f: A -> B) (x y : A), eq A x y -> eq B (f x) (f y).
  intros.
  apply eq_ind A x y (fun (a: A) => eq B (f x) (f a)).
    exact H.
    simpl. exact (eq_refl B (f x)).
Qed.