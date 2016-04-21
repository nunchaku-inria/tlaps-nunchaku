---------------------------- MODULE simpleLogic ----------------------------

CONSTANT a, b, P(_)

LEMMA L1 == (a = b) => (P(a) = P(b)) OBVIOUS

LEMMA L2 == ASSUME NEW c, NEW d PROVE (a=b => P(c)=P(d))

=============================================================================
\* Modification History
\* Last modified Thu Apr 21 19:39:40 CEST 2016 by Matthieu
\* Created Thu Apr 21 18:51:23 CEST 2016 by Matthieu
