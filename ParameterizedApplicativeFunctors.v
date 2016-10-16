Require Export JMeq FunctionalExtensionality.
Notation "x == y" := (JMeq.JMeq x y) (at level 70, no associativity).
Lemma JMeq_ext : forall (X Y Z : Type) (Pf : Y = Z) (f : X -> Y) (g : X -> Z), 
  (forall x, (f x == g x)) -> f == g.
Proof.
 intros; subst.
 match goal with
 | [ |- ?f == ?g ] =>
   cut (f = g); [intros; subst; reflexivity | idtac]
 end.
 apply functional_extensionality.
 intros;
 apply JMeq_eq;
 auto.
Qed.
  
Definition compose : forall {A B C : Type}, (B -> C) -> (A -> B) -> A -> C :=
  fun _ _ _ g f x => g (f x).
Infix "<o>" := compose (at level 40, left associativity).

Module Type Monoid.
  Parameter A : Type.
  Parameter Dot : A -> A -> A.
  Infix "dot" := Dot (at level 50, left associativity).
  Parameter Unit : A.
  Axiom Dot_assoc : forall a b c, a dot b dot c = a dot (b dot c).
  Axiom Left_Unit : forall (x : A), x dot Unit = x.
  Axiom Right_Unit : forall (x : A), Unit dot x = x.
End Monoid.

Module Type PFunctor.
  Parameter P : Type.
  Parameter F : P -> Type -> Type.
  Parameter Map : forall {A B : Type}, (A -> B) -> forall {p : P}, F p A -> F p B.
  Infix "<$>" := Map (at level 50, left associativity).
  Axiom Map_id : forall (A : Type) (p : P), Map (id (A := A)) = id (A := F p A).
  Axiom Map_compose : forall (A B C : Type) (p : P) (f : A -> B) (g : B -> C), Map g <o> Map f = Map (p := p) (g <o> f).
End PFunctor.

Module FuncCompose
       (F : PFunctor)
       (G : PFunctor with Definition P := F.P)
  : PFunctor
    with Definition P := F.P
    with Definition F := fun (p : F.P) => F.F p <o> G.F p
    with Definition Map := fun {A B : Type} f {p} => F.Map (p := p) (G.Map (A := A) (B := B) (p := p) f).
      Definition P := F.P.
      Definition F (p : P) := F.F p <o> G.F p.
      Definition Map {A B : Type} f {p} := F.Map (p := p) (G.Map (A := A) (B := B) (p := p) f).
      Infix "<$>" := Map (at level 50, left associativity).
      Theorem Map_id : forall (A : Type) (p : P), Map (id (A := A)) = id (A := F p A).
      Proof.
        intros.
        unfold Map.
        rewrite G.Map_id.
        apply F.Map_id.
      Qed.
      Theorem Map_compose : forall (A B C : Type) (p : P) (f : A -> B) (g : B -> C),
          Map g <o> Map f = Map (p := p) (g <o> f).
      Proof.
        intros.
        unfold Map.
        rewrite <- G.Map_compose.
        apply F.Map_compose.
      Qed.
End FuncCompose.

Module Type PAppFunc.
  Declare Module Mon : Monoid.
  Infix "dot" := Mon.Dot (at level 50, left associativity).
  Definition one := Mon.Unit.
  Declare Module Func : PFunctor with Definition P := Mon.A.
  Definition M := Func.F.
  Definition P := Func.P.
  Infix "<$>" := Func.Map (at level 50, left associativity).
  Parameter Pure : forall {A : Type}, A -> M one A.
  Parameter App : forall {A B : Type} {p : P}, M p (A -> B) -> forall {q : P}, M q A -> M (p dot q) B.
  Axiom Map_PureApp : forall (A B : Type) (p : P) (f : A -> B),
      Func.Map (p := p) f == App (q := p) (Pure f).
  Axiom Homomorphism : forall (A B : Type) (p : P) (f : A -> B) (x : A),
      f <$> (Pure x) = Pure (f x).
  Axiom Interchange : forall (A B : Type) (p : P) (u : M p (A -> B)) (x : A),
      App u (Pure x) == (fun f => f x) <$> u.
  Axiom Composition : forall (A B C : Type) (p q r : P) (u : M p (B -> C)) (v : M q (A -> B)),
      App (q := r) (App ((fun f g x => f (g x)) <$> u) v) == (App u) <o> (App (q := r) v).
End PAppFunc.

Module AppFunc_Theorems (AF : PAppFunc).
  Import AF.
  Corollary Identity : forall (A : Type) (p : P),
      App (B := A) (q := p) (Pure (fun x => x)) == fun (x : M p A) => x.
  Proof.
    intros.
    apply (JMeq.JMeq_trans (y := Func.Map (p := p) (fun (x : A) => x))).
    symmetry;
    apply Map_PureApp.
    match goal with
    | [ |- ?x == ?y ] =>
      cut (x = y);
        [generalize x y; intros; subst; reflexivity
        | apply Func.Map_id]
    end.
  Qed.
  Corollary MapApp : forall (A B C : Type) (p q : P) (u : B -> C) (v : M p (A -> B)),
      (Func.Map u) <o> (App (q := q) v) = App (Func.Map (fun g x => u (g x)) v).
  Proof.
    intros.
    apply JMeq_eq.
    apply (JMeq.JMeq_trans (y := App (Pure u) <o> App (q := q) v)).
    match goal with
    | [ |- ?f <o> _ == ?g <o> _ ] =>
      cut (f == g); [generalize f g | apply Map_PureApp]
    end.
    rewrite Mon.Right_Unit;
    intros; subst; reflexivity.
    rewrite <- Composition.
    rewrite Homomorphism; try assumption.
    match goal with
    | [ |- App (App (Pure ?f) _) == App (?g <$> _)] =>
      cut (Func.Map (p := p) g == App (q := p) (Pure f));
        [generalize (Func.Map (p := p) g) (App (q := p) (Pure f))
        | apply Map_PureApp]
    end.
    rewrite Mon.Right_Unit;
    intros; subst; reflexivity.
  Qed.
  Corollary AppMap : forall (A B C : Type) (p q : P) (u : M p (B -> C)) (v : A -> B),
      (App u) <o> (Func.Map (p := q) v) = App ((fun f : B -> C => f <o> v) <$> u).
  Proof.
    intros.
    apply JMeq_eq.
    apply (JMeq.JMeq_trans (y := App u <o> App (q := q) (Pure v))).
    match goal with
    | [ |- _ <o> ?f == _ <o> ?g ] =>
      cut (f == g); [generalize f g | apply Map_PureApp]
    end.
    rewrite Mon.Right_Unit;
    intros; subst; reflexivity.
    rewrite <- Composition.
    match goal with
    | [ |- App ?f == App ?g ] =>
      cut (f == g); [generalize f g | idtac]
    end.
    rewrite Mon.Left_Unit;
    intros; subst; reflexivity.
    eapply JMeq.JMeq_trans.
    apply Interchange.
    match goal with
    | [ |- context [?f <$> (?g <$> u)] ] =>
      change (f <$> (g <$> u)) with ((Func.Map f <o> Func.Map g) u)
    end.
    rewrite Func.Map_compose.
    reflexivity.
  Qed.
End AppFunc_Theorems.

Module AppCompose
       (F : PAppFunc)
       (G : PAppFunc with Module Mon := F.Mon)
  : PAppFunc.
      Module Mon := F.Mon.
      Definition one := Mon.Unit.
      Infix "dot" := Mon.Dot (at level 50, left associativity).
      Module Func := FuncCompose F.Func G.Func.
      Definition M := Func.F.
      Definition P := Func.P.
      Infix "<$>" := Func.Map (at level 50, left associativity).
      Definition Pure {A : Type} :=
        F.Pure <o> G.Pure (A := A).
      Definition App {A B : Type} {p : P} (u : M p (A -> B)) {q} :=
        F.App (q := q) (F.Func.Map (fun f => G.App (q := q) f) u).
      Theorem Map_PureApp : forall (A B : Type) (p : P) (f : A -> B),
          Func.Map (p := p) f == App (q := p) (Pure f).
      Proof.
        intros.
        unfold App;
        unfold Func.Map;
        unfold Pure;
        unfold compose.
        rewrite <- F.Homomorphism; try assumption.
        match goal with
        | [ |- context [F.Func.Map ?f (F.Func.Map ?g ?m)]] =>
          change (F.Func.Map f (F.Func.Map g m))
          with ((F.Func.Map f <o> (F.Func.Map g)) m)
        end.
        rewrite F.Func.Map_compose;
        unfold compose.
        rewrite F.Homomorphism; try assumption.
        symmetry.
        eapply JMeq.JMeq_trans.
        symmetry.
        apply F.Map_PureApp.
        match goal with
        | [ |- F.Func.Map ?g == F.Func.Map ?h ] =>
          cut (h == g); [generalize h g | apply (G.Map_PureApp _ _ p f)]
        end.
        rewrite F.Mon.Right_Unit;
        intros;
        subst;
        reflexivity.
      Qed.
      Theorem Homomorphism : forall (A B : Type) (p : P) (f : A -> B) (x : A),
          f <$> (Pure x) = Pure (f x).
      Proof.
        intros.
        unfold Func.Map;
        unfold Pure;
        unfold compose.
        rewrite <- G.Homomorphism; try assumption.
        rewrite F.Homomorphism; try assumption.
        reflexivity.
      Qed.        
      Theorem Interchange : forall (A B : Type) (p : P) (u : M p (A -> B)) (x : A),
          App u (Pure x) == (fun f => f x) <$> u.
      Proof.
        intros.
        unfold Pure;
        unfold compose;
        unfold App;
        unfold Func.Map.
        eapply JMeq.JMeq_trans.
        match goal with
        | [ |- F.App ?h (F.Pure ?y) == _ ] =>
          apply (F.Interchange _ _ _ h y)
        end.
        match goal with
        | [ |- F.Func.Map ?h (F.Func.Map ?g ?y) == _ ] =>
          change (F.Func.Map h (F.Func.Map g y))
          with ((F.Func.Map h <o> (F.Func.Map g)) y);
            rewrite F.Func.Map_compose
        end.
        unfold compose.
        match goal with
        | [ |- F.Func.Map ?h u == F.Func.Map ?g u ] =>
          cut (h == g); [generalize h g | idtac]
        end.
        rewrite F.Mon.Left_Unit;
        intros; subst; reflexivity.
        apply JMeq_ext.
        rewrite F.Mon.Left_Unit;
        reflexivity.
        intros;
        apply G.Interchange.
      Qed.
      Module FTheorems := AppFunc_Theorems F.
      Ltac rewrite_map_compose :=
        match goal with
        | [ |- context [F.Func.Map ?f (F.Func.Map ?g ?v)] ] =>
          change (F.Func.Map f (F.Func.Map g v))
          with ((F.Func.Map f <o> (F.Func.Map g)) v);
            rewrite F.Func.Map_compose
        end.
      Theorem Composition : forall (A B C : Type) (p q r : P) (u : M p (B -> C)) (v : M q (A -> B)),
          App (q := r) (App ((fun f g x => f (g x)) <$> u) v) == App u <o> (App (q := r) v).
      Proof.
        intros.
        unfold Func.Map;
        unfold App at 2;
        rewrite_map_compose.
        unfold App at 1;
        match goal with
        | [ |- context [F.Func.Map ?f (F.App ?g ?u)] ] =>
          change (F.Func.Map f (F.App g u))
          with ((F.Func.Map f <o> F.App g) u)
        end;
        rewrite FTheorems.MapApp.
        rewrite_map_compose.
        unfold compose at 1 2.
        match goal with
        | [ |- F.App (q := ?r) (F.App (F.Func.Map ?f ?u) ?v) == _ ] =>
          apply (JMeq.JMeq_trans (y := F.App (q := r) (F.App (F.Func.Map (fun m n => (G.App m) <o> (G.App (q := r) n)) u) v)))
        end.
        match goal with
        | [ |- F.App (F.App (F.Func.Map ?f _) _) == F.App (F.App (F.Func.Map ?g _) _)] =>
          cut (f == g); [generalize f g | idtac]
        end.
        intros; subst.
        cut (G.M (p dot q dot r) C == G.M (p dot (q dot r)) C);
          [ generalize dependent (G.M (p dot q dot r) C)
          | clear; rewrite Mon.Dot_assoc; reflexivity].
        intros; repeat subst; reflexivity.
        repeat (apply JMeq_ext;
                 [rewrite Mon.Dot_assoc; reflexivity | intros]).
        match goal with
        | [ |- G.App (q := ?r) ?f _ == ?g _ ] =>
          cut (G.App (q := r) f == g);
            [ generalize (G.App (q := r) f) g
            | apply G.Composition]
        end.
        rewrite Mon.Dot_assoc;
          intros; subst; reflexivity.
        match goal with
        | [ |- context [(fun (m : G.M ?p (?B -> ?C)) (n : G.M ?q (?A -> ?B)) => G.App (q := ?h) m <o> G.App (q := ?r) n)] ] =>
        change (fun m n => G.App m <o> G.App (q := r) n)
        with ((fun P => P (fun (n : G.M q (A -> B)) => G.App (q := r) n)) <o> ((fun f g x => f (g x)) <o> (fun f g x => f (g x)) <o> (fun (m : G.M p (B -> C)) => G.App (p := p) (q := h) m)))
        end.
        repeat (rewrite <- F.Func.Map_compose).
        unfold compose at -4.
        match goal with
        | [ |- F.App (q := ?z) (F.App (F.Func.Map (p := ?p) (fun P => P ?x) ?u) ?v) == _ ] =>
          apply (JMeq.JMeq_trans
                   (y := F.App (q := z) (F.App (F.App u (F.Pure x)) v)));
            [cut ((F.Func.Map (p := p) (fun P => P x) u) == F.App u (F.Pure x)) | idtac]
        end.
        match goal with
        | [ |- ?x == ?y -> _ ] => generalize x y
        end;
        rewrite Mon.Left_Unit;
        intros; subst; reflexivity.
        symmetry;
          apply F.Interchange.
        match goal with
        | [ |- F.App (q := ?rr) (F.App (q := ?qq) (F.App (F.Func.Map ?c ?uu) ?vv) ?ww) == _ ] =>
        apply (JMeq.JMeq_trans (y := F.App (q := rr) ((F.App uu <o> F.App vv) ww)))
        end.
        match goal with
        | [ |- F.App (F.App (q := ?q) ?f ?x) == F.App (?g ?x) ] =>
          cut (F.App (q := q) f == g); [generalize (F.App (q := q) f) g | apply F.Composition]
        end.
        rewrite Mon.Right_Unit;
          rewrite Mon.Left_Unit;
          intros; subst; reflexivity. 
        unfold compose at 1.
        match goal with
        | [ |- F.App (q := ?r) (F.App (F.Func.Map _ ?u) ?v) == _ ] =>
          apply (JMeq.JMeq_trans (y := F.App u <o>
                                       F.App (q := r) v));
            [apply F.Composition | idtac]
        end.
        match goal with
        | [ |- ?u <o> ?v == ?x <o> ?y ] =>
          cut (u == x /\ v == y); [generalize u v x y | split]
        end.
        rewrite Mon.Right_Unit;
        intros ? ? ? ? [? ?];
        subst; reflexivity.
        rewrite Mon.Right_Unit;
        reflexivity.
        unfold App.
        match goal with
        | [ |- F.App (F.App (q := ?x) ?f _) == F.App (F.Func.Map (p := ?x) ?g _) ] =>
          cut (F.Func.Map (p := x) g == F.App (q := x) f);
            [generalize (F.App (q := x) f) (F.Func.Map (p := x) g) | apply F.Map_PureApp]
        end.
        rewrite Mon.Right_Unit;
          intros; subst; reflexivity.
      Qed.
End AppCompose.