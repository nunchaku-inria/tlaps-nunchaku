------------------------------- MODULE tests -------------------------------


CONSTANT P(_,_)

UQ(y) == \A x : P(x,y) 
UQB == \A x:P(x,x)

VARIABLE x

LEMMA ASSUME TRUE PROVE UQ(x) = UQB

=============================================================================
\* Modification History
\* Last modified Mon Apr 04 17:50:30 CEST 2016 by Matthieu
\* Created Wed Mar 23 16:18:29 CET 2016 by Matthieu
