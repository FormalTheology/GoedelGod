(*---------------------------------------------------------------------------*)
theory THEORYNAME
imports "~~/src/HOL/Library/TPTP"
begin
ML {* proofs := PROOFMODE *}

typedecl "mu"

lemma THEORYNAME:
  fixes "mnot" :: "
    ( ( 'i
      => bool )
    => ( 'i
      => bool ) )
  "

  assumes "mnot": "
    ( mnot
    = ( % Phi::( 'i
      => bool ).
        ( % W::'i.
          ( ~ ( Phi
               W ) ) ) ) )
  "

  fixes "mor" :: "
    ( ( 'i
      => bool )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mor": "
    ( mor
    = ( % Phi::( 'i
      => bool ).
        ( % Psi::( 'i
        => bool ).
          ( % W::'i.
            ( ( Phi
               W )
            | ( Psi
               W ) ) ) ) ) )
  "

  fixes "mbox" :: "
    ( ( 'i
      => ( 'i
        => bool ) )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mbox": "
    ( mbox
    = ( % R::( 'i
      => ( 'i
        => bool ) ).
        ( % Phi::( 'i
        => bool ).
          ( % W::'i.
            ( ALL V::'i.
              ( ( ~ ( ( R
                       W )
                     V ) )
              | ( Phi
                 V ) ) ) ) ) ) )
  "

  fixes "mforall_ind" :: "
    ( ( mu
      => ( 'i
        => bool ) )
    => ( 'i
      => bool ) )
  "

  assumes "mforall_ind": "
    ( mforall_ind
    = ( % Phi::( mu
      => ( 'i
        => bool ) ).
        ( % W::'i.
          ( ALL X::mu.
            ( ( Phi
               X )
             W ) ) ) ) )
  "

  fixes "mforall_indset" :: "
    ( ( ( mu
        => ( 'i
          => bool ) )
      => ( 'i
        => bool ) )
    => ( 'i
      => bool ) )
  "

  assumes "mforall_indset": "
    ( mforall_indset
    = ( % Phi::( ( mu
        => ( 'i
          => bool ) )
      => ( 'i
        => bool ) ).
        ( % W::'i.
          ( ALL X::( mu
          => ( 'i
            => bool ) ).
            ( ( Phi
               X )
             W ) ) ) ) )
  "

  fixes "mtrue" :: "
    ( 'i
    => bool )
  "

  assumes "mtrue": "
    ( mtrue
    = ( % W::'i.
        True ) )
  "

  fixes "mfalse" :: "
    ( 'i
    => bool )
  "

  assumes "mfalse": "
    ( mfalse
    = ( mnot
       mtrue ) )
  "

  fixes "mand" :: "
    ( ( 'i
      => bool )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mand": "
    ( mand
    = ( % Phi::( 'i
      => bool ).
        ( % Psi::( 'i
        => bool ).
          ( mnot
           ( ( mor
               ( mnot
                 Phi ) )
             ( mnot
               Psi ) ) ) ) ) )
  "

  fixes "mimplies" :: "
    ( ( 'i
      => bool )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mimplies": "
    ( mimplies
    = ( % Phi::( 'i
      => bool ).
        ( % Psi::( 'i
        => bool ).
          ( ( mor
             ( mnot
               Phi ) )
           Psi ) ) ) )
  "

  fixes "mimplied" :: "
    ( ( 'i
      => bool )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mimplied": "
    ( mimplied
    = ( % Phi::( 'i
      => bool ).
        ( % Psi::( 'i
        => bool ).
          ( ( mor
             ( mnot
               Psi ) )
           Phi ) ) ) )
  "

  fixes "mequiv" :: "
    ( ( 'i
      => bool )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mequiv": "
    ( mequiv
    = ( % Phi::( 'i
      => bool ).
        ( % Psi::( 'i
        => bool ).
          ( ( mand
             ( ( mimplies
                 Phi )
               Psi ) )
           ( ( mimplies
               Psi )
             Phi ) ) ) ) )
  "

  fixes "mxor" :: "
    ( ( 'i
      => bool )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mxor": "
    ( mxor
    = ( % Phi::( 'i
      => bool ).
        ( % Psi::( 'i
        => bool ).
          ( mnot
           ( ( mequiv
               Phi )
             Psi ) ) ) ) )
  "

  fixes "mdia" :: "
    ( ( 'i
      => ( 'i
        => bool ) )
    => ( ( 'i
        => bool )
      => ( 'i
        => bool ) ) )
  "

  assumes "mdia": "
    ( mdia
    = ( % R::( 'i
      => ( 'i
        => bool ) ).
        ( % Phi::( 'i
        => bool ).
          ( mnot
           ( ( mbox
               R )
             ( mnot
               Phi ) ) ) ) ) )
  "

  fixes "mexists_ind" :: "
    ( ( mu
      => ( 'i
        => bool ) )
    => ( 'i
      => bool ) )
  "

  assumes "mexists_ind": "
    ( mexists_ind
    = ( % Phi::( mu
      => ( 'i
        => bool ) ).
        ( mnot
         ( mforall_ind
           ( % X::mu.
              ( mnot
               ( Phi
                 X ) ) ) ) ) ) )
  "

  fixes "mvalid" :: "
    ( ( 'i
      => bool )
    => bool )
  "

  assumes "mvalid": "
    ( mvalid
    = ( % Phi::( 'i
      => bool ).
        ( ALL W::'i.
          ( Phi
           W ) ) ) )
  "

  fixes "mreflexive" :: "
    ( ( 'i
      => ( 'i
        => bool ) )
    => bool )
  "

  assumes "mreflexive": "
    ( mreflexive
    = ( % R::( 'i
      => ( 'i
        => bool ) ).
        ( ALL S::'i.
          ( ( R
             S )
           S ) ) ) )
  "

  fixes "msymmetric" :: "
    ( ( 'i
      => ( 'i
        => bool ) )
    => bool )
  "

  assumes "msymmetric": "
    ( msymmetric
    = ( % R::( 'i
      => ( 'i
        => bool ) ).
        ( ALL S::'i.
          ( ALL T::'i.
            ( ( ( R
                 S )
               T )
            --> ( ( R
                 T )
               S ) ) ) ) ) )
  "

  fixes "mtransitive" :: "
    ( ( 'i
      => ( 'i
        => bool ) )
    => bool )
  "

  assumes "mtransitive": "
    ( mtransitive
    = ( % R::( 'i
      => ( 'i
        => bool ) ).
        ( ALL S::'i.
          ( ALL T::'i.
            ( ALL U::'i.
              ( ( ( ( R
                     S )
                   T )
                & ( ( R
                     T )
                   U ) )
              --> ( ( R
                   S )
                 U ) ) ) ) ) ) )
  "

  fixes "rel_s5" :: "
    ( 'i
    => ( 'i
      => bool ) )
  "

  fixes "mbox_s5" :: "
    ( ( 'i
      => bool )
    => ( 'i
      => bool ) )
  "

  assumes "mbox_s5": "
    ( mbox_s5
    = ( % Phi::( 'i
      => bool ).
        ( % W::'i.
          ( ALL V::'i.
            ( ( ~ ( ( rel_s5
                     W )
                   V ) )
            | ( Phi
               V ) ) ) ) ) )
  "

  fixes "mdia_s5" :: "
    ( ( 'i
      => bool )
    => ( 'i
      => bool ) )
  "

  assumes "mdia_s5": "
    ( mdia_s5
    = ( % Phi::( 'i
      => bool ).
        ( mnot
         ( mbox_s5
           ( mnot
             Phi ) ) ) ) )
  "

  assumes "a1": "
    ( mreflexive
     rel_s5 )
  "

  assumes "a2": "
    ( mtransitive
     rel_s5 )
  "

  assumes "a3": "
    ( msymmetric
     rel_s5 )
  "

  fixes "god" :: "
    ( mu
    => ( 'i
      => bool ) )
  "

  fixes "positive" :: "
    ( ( mu
      => ( 'i
        => bool ) )
    => ( 'i
      => bool ) )
  "

  fixes "essential" :: "
    ( ( mu
      => ( 'i
        => bool ) )
    => ( mu
      => ( 'i
        => bool ) ) )
  "

  fixes "nec_exists" :: "
    ( mu
    => ( 'i
      => bool ) )
  "

  assumes "axiom_1": "
    ( mvalid
     ( mforall_indset
       ( % P::( mu
        => ( 'i
          => bool ) ).
          ( mforall_indset
           ( % Q::( mu
            => ( 'i
              => bool ) ).
              ( ( mimplies
                 ( ( mand
                     ( positive
                       P ) )
                   ( mbox_s5
                     ( mforall_ind
                       ( % X::mu.
                          ( ( mimplies
                             ( P
                               X ) )
                           ( Q
                             X ) ) ) ) ) ) )
               ( positive
                 Q ) ) ) ) ) ) )
  "

  assumes "axiom2": "
    ( mvalid
     ( mforall_indset
       ( % P::( mu
        => ( 'i
          => bool ) ).
          ( ( mequiv
             ( positive
               P ) )
           ( mnot
             ( positive
               ( % W::mu.
                  ( mnot
                   ( P
                     W ) ) ) ) ) ) ) ) )
  "

  assumes "def_1": "
    ( god
    = ( % X::mu.
        ( mforall_indset
         ( % P::( mu
          => ( 'i
            => bool ) ).
            ( ( mimplies
               ( positive
                 P ) )
             ( P
               X ) ) ) ) ) )
  "

  assumes "axiom_3": "
    ( mvalid
     ( positive
       god ) )
  "

  assumes "def_2": "
    ( essential
    = ( % P::( mu
      => ( 'i
        => bool ) ).
        ( % X::mu.
          ( ( mand
             ( P
               X ) )
           ( mforall_indset
             ( % Q::( mu
              => ( 'i
                => bool ) ).
                ( ( mimplies
                   ( Q
                     X ) )
                 ( mbox_s5
                   ( mforall_ind
                     ( % Y::mu.
                        ( ( mimplies
                           ( P
                             Y ) )
                         ( Q
                           Y ) ) ) ) ) ) ) ) ) ) ) )
  "

  assumes "axiom_4": "
    ( mvalid
     ( mforall_indset
       ( % P::( mu
        => ( 'i
          => bool ) ).
          ( ( mimplies
             ( positive
               P ) )
           ( mbox_s5
             ( positive
               P ) ) ) ) ) )
  "

  assumes "def_3": "
    ( nec_exists
    = ( % X::mu.
        ( mforall_indset
         ( % P::( mu
          => ( 'i
            => bool ) ).
            ( ( mimplies
               ( ( essential
                   P )
                 X ) )
             ( mbox_s5
               ( mexists_ind
                 ( % Y::mu.
                    ( P
                     Y ) ) ) ) ) ) ) ) )
  "

  assumes "axiom_5": "
    ( mvalid
     ( positive
       nec_exists ) )
  "

(* This is the conjecture *)
  shows (* "theorem_1": *) "
    ( mvalid
     ( mbox_s5
       ( mexists_ind
         ( % X::mu.
            ( god
             X ) ) ) ) )
  "

  apply (insert assms)
  apply (tactic {* isabellep_tac @{context} @{claset} @{simpset} @{clasimpset} CPULIMIT *})
  done
  prf THEORYNAME
  ML_command {* writeln ("% SZS status Theorem for FILENAME : " ^ Context.theory_name @{theory}) *}
  ML_command {* writeln ("% SZS output start Proof for FILENAME") *}
  prf THEORYNAME
  ML_command {* writeln ("% SZS output end Proof for FILENAME") *}
end
(*---------------------------------------------------------------------------*)
