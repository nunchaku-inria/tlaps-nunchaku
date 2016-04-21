------------------------------- MODULE tests -------------------------------
(*
 THEOREM TRUE OBVIOUS

 THEOREM FALSE OBVIOUS

 THEOREM ASSUME FALSE PROVE FALSE OBVIOUS

 THEOREM 1=1 OBVIOUS

 THEOREM 1=2 OBVIOUS

THEOREM \E x \in {0,1}: x=3 OBVIOUS

LEMMA \A x : x = x OBVIOUS
*)

THEOREM \A p, q, r : (p => q) /\ (q => r) => (p => r) OBVIOUS

THEOREM INTER == \A p, q : (p => q) => (\E i : (p => i) /\ (i => q) /\ ~(i => p) /\ ~(p => i) ) OBVIOUS

=============================================================================
\* Modification History
\* Last modified Tue Apr 05 16:03:20 CEST 2016 by Matthieu
\* Created Wed Mar 23 16:18:29 CET 2016 by Matthieu
