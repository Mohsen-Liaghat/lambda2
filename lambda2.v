Import Nat.
Require Import List.
Import ListNotations.

Definition atomic_type := nat.
Definition atomic_term := nat.

Inductive type : Type :=
    | var ( n : atomic_type ) 
    | arr ( t1 t2 : type ) 
    | pi ( v : atomic_type ) ( t : type ).

Inductive term : Type :=
    | tvar ( n : atomic_term )
    | app ( t1 t2 : term )
    | Tapp ( t1 : term ) ( t2 : type )
    | abs ( n : atomic_term ) ( T : type ) ( t : term )
    | Tabs ( n : atomic_type ) ( t : term ).

Inductive statement : Type :=
    | st ( T : type )
    | stt ( t : term ) ( T : type ).
    
Inductive declaration : Type :=
    | std ( T : atomic_type )
    | sttd ( t : atomic_term ) ( T : type ).

Definition context := list declaration.

Fixpoint check_type ( g : context ) ( t : atomic_type ) : bool := 
    match g with 
    | [] => false
    | d :: g' => 
        match d with 
        | sttd _ _ => check_type g' t 
        | std n => eqb n t || check_type g' t
        end
    end.

Fixpoint check_term ( g : context ) ( x : atomic_term ) : bool := 
    match g with
    | [] => false 
    | d :: g' => match d with 
        | sttd y _ => eqb x y || check_term g' x 
        | std _ => check_term g' x 
        end
    end.

Fixpoint fvl ( t : type ) : list atomic_type :=
    match t with 
    | var v => [v]
    | arr a b => fvl a ++ fvl b 
    | pi n t' => remove PeanoNat.Nat.eq_dec n ( fvl t' )
    end.

Definition foreach { T : Type } ( l : list T ) ( P : T -> bool ) := fold_left andb ( map P l) true = true.

Inductive l2_context : context -> Prop :=
    | emp : l2_context []
    | l2T  ( g : context ) ( a : atomic_type ) : l2_context g -> check_type g a = false -> l2_context ((std a) :: g)
    | l2t ( g : context ) ( x : atomic_term ) ( r : type ) : l2_context g -> check_term g x = false -> foreach ( fvl r ) ( check_type g ) -> l2_context (( sttd x r ) :: g ).

Fixpoint substitution ( T : type ) ( x : atomic_type ) ( s : type ) : type :=
    match T with
    | var n => if (eqb n x) then s else var n
    | arr t1 t2 => arr ( substitution t1 x s ) ( substitution t2 x s )
    | pi v t => if ( eqb v x ) then pi v t else pi v ( substitution t x s )
    end.

Inductive l2derivation : context -> statement -> Prop :=
    | dvar { g : context } { x : atomic_term } { s : type } : l2_context g -> In ( sttd x s ) g -> l2derivation g (stt (tvar x) s ) 
    | dappl { g : context } { m n : term } { s t : type } : l2derivation g ( stt m ( arr s t ) ) -> l2derivation g ( stt n s ) -> l2derivation g ( stt ( app m n ) t) 
    | dabst { g : context } { x : atomic_term } { s t : type } { m : term } : l2derivation ( sttd x s :: g ) ( stt m t ) -> l2derivation g ( stt ( abs x s m ) ( arr s t ) )
    | dform { g : context } { b : type } : l2_context g -> foreach ( fvl b ) ( check_type g ) -> l2derivation g ( st b )
    | dappl2 { g : context } { m : term } { a : atomic_type } { A t : type } : l2derivation g (stt m ( pi a A ) ) -> l2derivation g ( st t ) -> l2derivation g ( stt ( Tapp m t ) ( substitution A a t ) )
    | dabst2 { g : context } { a : atomic_type } { A : type } { m : term } : l2derivation ( ( std a ) :: g ) ( stt m A ) -> l2derivation g ( stt ( Tabs a m ) ( pi a A )).

Theorem l2_context_stability { g : context } { l : term } { s : type } : l2derivation g ( stt l s ) -> l2_context g.
Proof.
    intro h.
    induction h.
    { (* dvar *)
        exact H. 
    }
    { (* dappl *)
        exact IHh1.
    }
    { (* dabst *)
        inversion IHh.
        exact H2.
    }
    { (* dform *)
        exact H.
    }
    { (* dappl2 *)
        exact IHh1.
    }
    { (* dabst2 *)
        inversion IHh.
        exact H1.
    }
Qed.
