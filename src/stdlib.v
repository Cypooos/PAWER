Lemma IdProp : forall P: Prop, P -> P.
intros P p. exact p.
Qed.

Inductive False : Prop := .
Inductive True : Prop := I: True.

Definition not (A: Prop) := A -> False.

Inductive and (A: Prop) (B: Prop) : Prop := conj : A -> B -> and A B.

Lemma proj1 : forall A B: Prop, and A B -> A.
intros. exact (match H as _ in and _ _ return A with | conj _ _ a _ => a end).
Qed.

Lemma proj2 : forall A B: Prop, and A B -> B.
intros. exact (match H as _ in and _ _ return B with | conj _ _ _ b => b end).
Qed.

Lemma and_comm : forall A B: Prop, and A B -> and B A.
intros. exact (match H as _ in and _ _ return and B A with | conj _ _ a b => conj B A b a end).
Qed.

Inductive or (A: Prop) (B: Prop) : Prop := or_introl : A -> or A B | or_intror : B -> or A B.

Lemma or_comm : forall A B: Prop, or A B -> or B A.
intros. exact (match H as _ in or _ _ return or B A with
    | or_introl _ _ a => or_intror B A a
    | or_intror _ _ b => or_introl B A b
end).
Qed.

Inductive eq (A: Type({})) (x:A) : A -> Prop := eq_refl : eq A x x.

Lemma eq_ind : forall (A: Set) (x y: A) (P: A -> Prop), eq A x y -> P x -> P y.
intros. exact (match H as _ in eq _ _ a return P a with | eq_refl _ _ => H1 end).
Qed.

Lemma f_equal : forall (A B: Set) (f: A -> B) (x y : A), eq A x y -> eq B (f x) (f y).
intros.
apply eq_ind A x y (fun (a: A) => eq B (f x) (f a)).
  exact H.
  simpl. exact (eq_refl B (f x)).
Qed.

Inductive nat : Set := 0 : nat | S : nat -> nat.

Definition 1 := S 0.
Definition 2 := S 1.
Definition 3 := S 2.
Definition 4 := S 3.
Definition 5 := S 4.
Definition 6 := S 5.
Definition 7 := S 6.
Definition 8 := S 7.
Definition 9 := S 8.
Definition 10 := S 9.

Fixpoint add (n m:nat) {{struct n}} : nat :=
  match n as n in _ return nat with
  | 0 => m
  | S p => S (add p m)
  end.