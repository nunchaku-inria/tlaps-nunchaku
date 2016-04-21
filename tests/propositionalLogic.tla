------------------------- MODULE propositionalLogic -------------------------

THEOREM IMP == \A p, q : (p => q) <=> ( ~p \/ q ) OBVIOUS
\* goal forall (p:u) (q:u). is_true ( iff (imp p q) (disj (not p) (q)) ).

THEOREM MORGAN1 == \A p, q : ~(p /\ q) <=> ( ~p \/ ~q ) OBVIOUS
\* goal forall (p:u) (q:u). is_true ( iff (not (conj p q)) (disj (not p) (not q))  ).

THEOREM MORGAN2 == \A p, q : ~(p \/ q) <=> ( ~p /\ ~q ) OBVIOUS
\* goal forall (p:u) (q:u). is_true ( iff (not (disj p q)) (conj (not p) (not q))  ).

THEOREM INTER == \A p, q : (p => q) => (\E i : (p => i) /\ (i => q)) OBVIOUS
\* goal forall (p:u) (q:u). (is_true (imp p q)) => (exists x. (is_true (imp p x)) && (is_true (imp x q))).

=============================================================================
\* Modification History
\* Last modified Thu Apr 21 18:51:27 CEST 2016 by Matthieu
\* Created Tue Apr 19 16:01:54 CEST 2016 by Matthieu
