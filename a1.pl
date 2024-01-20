/* Membership */

mem(X,[]) :- fail.
mem(X,[X|_]) :- !.
mem(X,[_|R]) :- mem(X,R).

/*PART A*/

/*Reflexive transitive closure*/
mem((X,X),rtc(R),S) :- mem(X,S), !.
mem((X,Y),rtc(R),S) :- mem((X,Y),R),!.
mem((X,Y),rtc(R),S) :- mem((X,Z),R) , mem((Z,Y), rtc(R),S), !.

/*Reflexive transitive symmetric closure*/
mem((Y,X), inv(R),S) :- mem((X,Y), R).

mem((X,X),e(R),S) :- mem(X,S), !.
mem((X,Y),e(R),S) :- mem((X,Y),R),!.
mem((X,Y),e(R),S) :- mem((Y,X),rtc(R),S),!.
mem((X,Y),e(R),S) :- mem((X,Z),R) , mem((Z,Y), e(R),S), !.

/*Sets*/

/*subsets*/
subset([],S) :- !.
subset([X|R],S) :- mem(X,S) ,subset(R,S).

/*equal sets*/
eqsets([],[]) :- !.
eqsets(X,Y) :- subset(X,Y), subset(Y,X).

/*delete*/
del(X,[],[]) :- !.
del(X,[X|S1],S2) :- del(X,S1,S2),!.
del(X,[Y|S1],[Y|S2]) :- del(X,S1,S2),!.

/*remove duplicates*/

/*
remdup([],[]) :- !.
remdup([X|S1],S2) :- del(X,S1,T),remdup(T,S2). 
*/

remdups([],[]) :- !.
remdups([X|R],[X|Z]) :- del(X,R,L), remdups(L,Z).

/*union membership*/
mem(X,union(S1,S2)) :- mem(X,S1).
mem(X,union(S1,S2)) :- mem(X,S2).

/*union - assuming no duplicates in S1 and S2*/
union([ ], S2, S2) :- !.
union(S1, [ ], S1) :- !.
union([X|R], S2, [X|Z]) :- del(X, S2, S3),  union(R, S3, Z).

/*append - answer will have repeats */
append( [ ], L, L).
append( [X|R], L, [X|Z]) :- append(R, L, Z).

/* mapcons(X,L1, L2) --  cons the element X to each list in L1 to get L2 */
mapcons(X, [ ], [ ]) :- !.
mapcons(X, [Y|R], [ [X|Y] | Z ]) :- mapcons(X, R, Z).


/* power( S, P1): Here is an implementation of powerset of S */
power([ ], [ [ ] ]) :- !.
power([X|R], P) :- power(R, P1),  mapcons(X, P1, P2), append(P2, P1, P).