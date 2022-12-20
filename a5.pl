https://powcoder.com
代写代考加微信 powcoder
Assignment Project Exam Help
Add WeChat powcoder
Q2: Implication Form

A formula psi is in "implication form" iff psi is either

       (1) a literal, or
       
       (2) an implication implies( psi1, psi2)
           whose antecedent psi1 is a conjunction of literals,
           and whose succedent psi2 is a literal,
           
   where a literal is a variable or the negation of a variable.

Q2a.
Write Prolog predicates  conjlit( Phi) and
                         impform( Psi)
where
  literal( Phi)  is true iff Phi is either v(_) or not(v(_))

  conjlit( Phi)  is true iff Phi is a literal,
                             or Phi is  and( Phi1, Phi2)
                             where both Phi1 and Phi2 are conjunctions of literals

  impform( Psi)  is true iff Psi is a literal, or
                             Psi is an implication  implies( Psi1, Psi2)
                               where Psi1 is a literal or a conjunction of literals,
                               and Psi2 is a literal.

All of these predicates only need to work in the "input moding":
  you can assume that Phi and Psi are concrete data, not Prolog variables.

We have written  literal  for you.
*/

literal( v(_) ).
literal( not(v(_)) ).






/*
Q3: Tiny Theorem Prover
*/


/*
  prove(Ctx, P, Deriv):
    true if, assuming everything in Ctx is true,
     the formula p is true according to the rules given in a5.pdf,
     where Deriv represents the rules used.
     
     (This  *roughly* corresponds to the rules in
     a proof in the style of (pre-2020?) CISC 204,
     with the following rough correspondence:

        premise          use_assumption
        copy             use_assumption
        ->i              implies_right
        ->e              implies_left
        /\i              and_right
        /\e1, /\e2       and_left
        top i            top_right
     )
     
  This is the cool part:
    *each rule becomes a Prolog clause*.

  There is no "problem solving" where someone (like the instructor)
    figures out a strategy for applying Left and Right rules without getting
    into an infinite loop.

  In Prolog, we can write one clause for each logical rule, and it "just works".
*/

/*                          P in Ctx
                          ––––––––––––
 rule 'UseAssumption'       Ctx |- P
*/
prove( Ctx, P, use_assumption(P)) :- member( P, Ctx).

/*                       ––––––––––
  rule 'Top-Right'       Ctx |- top
*/
prove( _,   top, top_right).

/*
  We will use append "backwards":
  instead of taking concrete lists
  provided in a query, we take a concrete *appended* list Ctx
  and use append to "split up" the Ctx.
*/

/*
Q3a:
  Write Prolog clauses that correspond to the rules

    And-Right,
    Implies-Right.
*/

/*
  rule 'And-Right'
               Ctx |- Q1     Ctx |- Q2
               -----------------------
  CONCLUSION:    Ctx |- and(Q1, Q2)

  Put the result of prove on Ctx |- Q1 into Deriv1,
  and the result of prove on Ctx |- Q2 into Deriv2.
*/
prove(Ctx, and(Q1, Q2), and_right(Deriv1, Deriv2) :-
  change_this
  .



/*
  rule 'Implies-Right'
                  [P | Ctx] |- Q
               -------------------------
  CONCLUSION:     Ctx |- implies(P, Q)

  Put the result of prove on [P | Ctx] |- Q into Deriv,
  and return implies_right(Deriv).
*/





/*
  rule 'And-Left'
                          CtxP12
                 vvvvvvvvvvvvvvvvvvvvvvvv
                 Ctx1 ++ [P1, P2] ++ Ctx2 |- Q
               ----------------------------------
  CONCLUSION:  Ctx1 ++ [and(P1, P2)] ++ Ctx2 |- Q
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^    ^
               1st argument to prove            2nd argument to prove
*/
prove( Ctx, Q, and_left(Deriv)) :-
  append( Ctx1, [and(P1, P2) | Ctx2], Ctx),    %  Ctx1 ++ [and(P1, P2) | Ctx2]  ==  Ctx
  
  append( Ctx1, [P1 | [P2 | Ctx2]], CtxP12),   %  Ctx1 ++ [P1 | [P2 | Ctx2]]    ==  CtxP12
  prove( CtxP12, Q, Deriv).





/*
  Q3b: Implies-Left
*/

/*
  rule 'Implies-Left'
               Ctx1 ++ Ctx2 |- P1     Ctx1 ++ [P2] ++ Ctx2 |- Q
               ------------------------------------------------
   CONCLUSION:     Ctx1 ++ [implies(P1, P2)] ++ Ctx2 |- Q

   In the third argument, return implies_left(Deriv1, Deriv2)
     where Deriv1 is produced by calling prove on P1,
     and Deriv2 is produced by calling prove on P2.
*/







/*
  ?- prove([implies(v(b), v(h))], implies(v(b), v(h)), Deriv).
  Deriv = use_assumption(implies(v(b), v(h))) ;
   % CISC 204-style proof:
   %    1. implies(v(b), v(h))     premise       use_assumption
   % 
  Deriv = implies_right(implies_left(use_assumption(v(b)), use_assumption(v(h)))) ;
   % CISC 204-style proof:
   %     ____________________________________
   % 1  | v(b)                    assumption |   use_assumption(v(b))
   % 2  | implies(v(b), v(h))     premise    |
   % 3  | v(h)                    ->e 2, 1   |   use_assumption(v(h)) + implies_left
   %    |____________________________________|
   % 4   implies(v(b), v(h))      ->i 1-3        implies_right]
   %     
  false.

  ?- prove([v(d)], implies(and(v(b), v(b)), v(d)), Deriv).
  Deriv = implies_right(use_assumption(v(d))) ;
  Deriv = implies_right(and_left(use_assumption(v(d)))) ;
  false.

  ?- prove([implies(and(v(b), v(e)), v(d))], implies(v(b), v(h)), Deriv).
  false.

  ?- prove([and(and(v(a), v(b)), and(v(d), (v(e))))], v(d), Deriv).
  Deriv = and_left(and_left(and_left(use_assumption(v(d))))) ;
  Deriv = and_left(and_left(use_assumption(v(d)))) ;
  Deriv = and_left(and_left(and_left(use_assumption(v(d))))) ;
  false.
*/





/*
  BONUS (up to 5%):
  Implement the Or-Left-1, Or-Left-2, Or-Right rules from Assignment 3.
*/