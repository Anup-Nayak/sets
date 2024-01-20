/* Membership */
mem(X,[]) :- fail.
mem(X,[X|_]) :- !.
mem(X,[_|R]) :- mem(X,R).


mem(X,[],S) :- fail.
mem(X,[X|_],S) :- !.
mem(X,[_|R],S) :- mem(X,R,S).


/*test cases, examples*/

/*
?- mem(2,[2,3,4]).
true.

?- mem(5,[2,3,4]).
false.

?- mem((5,2),[(2,3),(3,4)]).
false.

?- mem((5,2),[(2,3),(5,2),(3,4)]).
true.

*/

/* SOME HELPFUL FUNCTIONS */

/*equal sets*/
eqsets([],[]) :- !.
eqsets(X,Y) :- subset(X,Y), subset(Y,X),!.

/*unequal sets*/
uneqsets(X,Y) :- not(eqsets(X,Y)).

/*TEST CASES*/
/*
?- eqsets([1,2,3],[1,2,3]).
true.

?- uneqsets([1,2,3],[1,2,3]).
false.

?- uneqsets([1,2,3],[1,2,3,4]).
true.

?- uneqsets([1,2,3,4],[1,2,3,4]).
false.

?- uneqsets([1,2,4,3],[1,2,3,4]).
false.

?- uneqsets([1,2,4,3],[1,3,3,4]).
true.

*/

/*PART A*/


/*  TRANSITIVE REFLEXIVE CLOSURE  */
mem((X,X),rt(R),S) :- mem(X,S,S),!.
mem((X,Y),rt(R),S) :- mem((X,Y),R,S),!.
mem((X,Y),rt(R),S) :- mem((X,Z),R,S) , del((X,Z),R,Z1), mem((Z,Y),tr(Z1),S),!.


/*transitive symmetric helper*/
mem((X,X),tr1(R),S) :- mem(X,S,S), !.
mem((X,Y),tr1(R),S) :- mem((X,Y),R,S),!.
mem((X,Y),tr1(R),S) :- mem((X,Z),R,S),mem((Z,Y),R,S),!.

/*helper*/
mem((X,Y),tr(R),S) :- mem((X,Z),tr1(R),S), mem((Z,Y),tr1(R),S),!.
mem((X,Y),tr(R),S) :- mem((X,Y),tr1(R),S),!.

/* TEST CASES */

/*

LET S = [1,2,3,4,5] and
R = [(1,2),(2,5),(3,1),(5,1)], 

so the reflexive transitive closure 
will contain elements:

[(1,1),(1,2),(1,5),
(2,1),(2,2),(2,5),
(3,1),(3,2),(3,3),(3,5)
(5,1),(5,2)].

?- mem((1,1),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((1,2),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((1,3),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((1,4),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((1,5),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,1),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,2),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,3),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((2,4),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((2,5),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,1),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,2),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,3),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,4),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((3,5),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((4,1),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((4,2),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((4,3),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((4,4),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((4,5),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((5,1),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((5,2),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((5,3),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((5,4),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((5,5),rt([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.


*/


/*  TRANSITIVE REFLEXIVE SYMMETRIC CLOSURE  */

mem((X,Y),eqc(R),S) :- mem((X,Y),rt(R),S),!.
mem((Y,X),eqc(R),S) :- mem((X,Y),rt(R),S),!.
mem((X,Y),eqc(R),S) :- mem((X,Z),rt(R),S), del((X,Z),rt(R),Z1), mem((Z,Y),eqc(Z1),S),!.

/*discarded*/
mem((X,Y),trs(R),S) :- mem((X,Z),rt(R),S), mem((Z,Y),rt(R),S),!.
mem((X,Y),trs(R),S) :- mem((Y,X),rt,S),!.
mem((Y,X),trs(R),S) :- mem((X,Z),rt(R),S), mem((Z,Y),rt(R),S),!.
mem((X,Y),trs(R),S) :- mem((X,Y),rt(R),S),!.

/*TEST CASES*/

/*
LET S = [1,2,3,4,5] and
R = [(1,2),(2,5),(3,1),(5,1)], 

so the reflexive transitive closure 
will contain elements:

[(1,1),(1,2),(1,3),(1,5),
(2,1),(2,2),(2,3),(2,5),
(3,1),(3,2),(3,3),(3,5),
(4,4),
(5,1),(5,2),(5,3),(5,5)].

?- mem((1,1),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((1,2),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((1,3),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((1,4),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((1,5),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,1),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,2),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,3),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((2,4),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((2,5),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,1),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,2),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,3),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((3,4),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((3,5),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((4,1),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((4,2),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((4,3),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((4,4),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((4,5),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((5,1),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((5,2),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

?- mem((5,3),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((5,4),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
false.

?- mem((5,5),eqc([(1,2),(2,5),(3,1),(5,1)]),[1,2,3,4,5]).
true.

*/

/*--------------------------------------------------------------------*/

/* PART B */

/*subsets*/
subset([],S) :- !.
subset([X|R],S) :- mem(X,S) ,subset(R,S),!.

/*TEST CASES */

/*
?- subset([],[]).
true.

?- subset([],[1,2]).
true.

?- subset([1],[]).
false.

?- subset([1,3,4],[1,2,3]).
false.

?- subset([1,3,4],[1,5,6,3]).
false.

?- subset([1,4],[1,2,3,4]).
true.

?- subset([4,2],[1,2,3,4]).
true.

?- subset([4,1],[1,2,3,4]).
true.

?- subset([(1,2),(3,5)],[(1,2),(6,2),(3,5)]).
true.

?- subset([(1,2),(3,5)],[(1,3),(3,5)]).
false.

*/

/*delete*/ 
del(X,[],[]) :- !.
del(X,[X|S1],S2) :- del(X,S1,S2),!.
del(X,[Y|S1],[Y|S2]) :- del(X,S1,S2),!.

remdups([],[]) :- !.
remdups([X|R],[X|Z]) :- del(X,R,L), remdups(L,Z).

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


/* power( S, P1): Here is an implementation of powerset of S 
ASSUMPTION - SET DOES NOT HAVE DUPLICATES
*/
powerI([ ], [ [ ] ]) :- !.
powerI([X|R], P) :- powerI(R, P1),  mapcons(X, P1, P2), append(P2, P1, P),!.

/* UNION AND POWER TEST CASES */

/*
1. UNION

-- TAKING BASE CASES AND THEN CASES THAT CHECK ALL POSSIBLE COMBINATIONS FOR UNION 
AND IT DOES NOT HAVE REPETETIONS (FOR SET OF ELEMENTS ONLY, NOT SET OF SETS AS SHOWN IN LAST EXAMPLE 
AS IT DOES NOT REALIZE THAT ORDERING HAS NO SIGNIFICANCE INSIDE SET OF SETS, E.G. BETWEEN [(a,b)] and [(b,a)].

?- union([],[],Z).
Z = [].

?- union([a],[],Z).
Z = [a].

?- union([a],[b],Z).
Z = [a, b].

?- union([1,2,3],[4,5],Z).
Z = [1, 2, 3, 4, 5].

?- union([1,2,3],[2,3,4,5],Z).
Z = [1, 2, 3, 4, 5].

?- union([1,2,3,4,5],[2,3,4,5],Z).
Z = [1, 2, 3, 4, 5].

?- union([1,2,3,4,6,7,5],[2,3,4,5,6,7],Z).
Z = [1, 2, 3, 4, 6, 7, 5].

?- union([(1,2),(2,3)],[(3,2),(1,2),(4,5)],Z).
Z = [(1, 2), (2, 3), (3, 2), (4, 5)].



2. POWER 

-- TAKING BASE CASES AND THEN CASES THAT CHECK ALL POSSIBLE COMBINATIONS FOR POWER

?- powerI([],Z).
Z = [[]].

?- powerI([1],Z).
Z = [[1], []].

?- powerI([1,2,3],Z).
Z = [[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [2], [3], []].

?- powerI([1,2,3,4],Z).
Z = [[1, 2, 3, 4], [1, 2, 3], [1, 2, 4], [1, 2], [1, 3, 4], [1, 3], [1, 4], [1], [2, 3, 4], [2, 3], [2, 4], [2], [3, 4], [3], [4], []].

?- powerI([1,2,3,4,5],Z).
Z = [[1, 2, 3, 4, 5], [1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 3], [1, 2, 4, 5], [1, 2, 4], [1, 2, 5], [1, 2], [1, 3, 4, 5], [1, 3, 4], [1, 3, 5], [1, 3], [1, 4, 5], [1, 4], [1, 5], [1], [2, 3, 4, 5], [2, 3, 4], [2, 3, 5], [2, 3], [2, 4, 5], [2, 4], [2, 5], [2], [3, 4, 5], [3, 4], [3, 5], [3], [4, 5], [4], [5], []].



*/


/*intersection helper - intersection of one element with list*/
ih(X,[],[]) :- !.
ih([],Y,[]) :- !.
ih(X,[X|R1],[X|Z]) :- ih([],R1,Z),!.
ih(X,[Y|R1],Z) :- ih(X,R1,Z). 

/*INTERSECTION*/

interI([],S2, []) :- !.
interI(S1,[], []) :- !.
interI([X|R1], S2, Z) :- ih(X,S2,M),interI(R1,S2,Z1),union(Z1,M,Z).  

% intersection([X|R1],[X|R2],[X|Z]) :- del(X,R2,R3),intersection(R1,R3,Z).
% intersection([X|R1],[Y|R2],Z) :- intersection([X|R1],R2,Z).

intersection(S1,S2,Z) :- interI(S1,S2,Z1), eqsets(Z1,Z),!. 

/* TEST CASES  */

/*
?- interI([],[],Z).
Z = [].

?- interI([],[a,b],Z).
Z = [].

?- interI([a,b],[],Z).
Z = [].

?- interI([a,b],[c,d],Z).
Z = [].

?- interI([a,b],[b,c,d],Z).
Z = [b].

?- interI([a,b,d],[c,d,b,y,g],Z).
Z = [d, b].

?- interI([4,3,2,1,7],[6,5,3,8],Z).
Z = [3].

?- interI([4,3,2,1,7],[6,5,3,7,8,4],Z).
Z = [7, 3, 4].

?- interI([1,2,2],[3,2,4],Z).
Z = [2].

?- interI([1,2,2],[4,2,3,2,4],Z).
Z = [2].

*/

/*set difference helper*/
sh(X,[],[X]) :- !.
sh([], X ,[]) :- !.
sh(X,[X|R2],Z) :- sh([],X,Z),!.
sh(X,[Y|R2],Z) :- sh(X,R2,Z).

/*SET DIFFERENCE*/

diffI(X,[],X) :- !.
diffI([],X,[]) :- !.
diffI([X|R1],S2,Z) :- sh(X,S2,M),diffI(R1,S2,Z1),union(M,Z1,Z).


setdiff(S1,S2,Z) :- diffI(S1,S2,Z1), eqsets(Z1,Z),!.

/*  TEST CASES  */

/*
?- diffI([],[],Z).
Z = [].

?- diffI([a,b],[],Z).
Z = [a, b].

?- diffI([],[a,b],Z).
Z = [].

?- diffI([a,b,c,d],[g,h,j],Z).
Z = [a, b, c, d].

?- diffI([a,b,c,d],[g,b,c,h,j],Z).
Z = [a, d].

?- diffI([a,b,c,d],[g,b,c,h,j,a,d],Z).
Z = [].

?- diffI([a,b,c,d],[g,b,j,a,d],Z).
Z = [c].

?- diffI([a,b,c,d],[g,b,j,a],Z).
Z = [c, d].

?- diffI([2,2,3],[2,5],Z).
Z = [3].

?- diffI([2,2,6,3],[2,6,6,5],Z).
Z = [3].

?- diffI([2,2,6,3,7,9],[2,6,6,5],Z).
Z = [3, 7, 9].

*/


/*CARTESIAN OF SETS */
cartesianI(X,[],[]) :- !.
cartesianI([],X, []):- !.
cartesianI([X|R1],[Y|R2],[(X,Y)|Z]) :- cartesianI([X|R1],R2,Z1),cartesianI(R1,[Y|R2],Z2),union(Z1,Z2,Z).

cartesian(S1,S2,Z) :- remdups(S1,S3),remdups(S2,S4),cartesianI(S3,S4,Z),!.

cart(S1,S2,Z) :- cartesian(S1,S2,Z1), eqsets(Z1,Z),!.

/* TEST CASES */

/*

?- cartesian([],[],Z).
Z = [].

?- cartesian([a],[],Z).
Z = [].

?- cartesian([],[a],Z).
Z = [].

?- cartesian([1,2,3,4,5],[],Z).
Z = [].

?- cartesian([],[a,b,c,d],Z).
Z = [].

?- cartesian([a],[b],Z).
Z = [(a, b)].

?- cartesian([1,2,3],[a,b,c],Z).
Z = [(1, a), (1, b), (1, c), (2, c), (3, c), (2, b), (3, b), (2, a), (3, a)].

?- cartesian([1,2,3,3],[a,b,c,d],Z).
Z = [(1, a), (1, b), (1, c), (1, d), (2, d), (3, d), (2, c), (3, c), (2, b), (3, b), (2, a), (3, a)].

?- cartesian([1,2,3,3],[a,b,c,c,d],Z).
Z = [(1, a), (1, b), (1, c), (1, d), (2, d), (3, d), (2, c), (3, c), (2, b), (3, b), (2, a), (3, a)].

?- cartesian([1,2,3],[a,b,c,d],Z).
Z = [(1, a), (1, b), (1, c), (1, d), (2, d), (3, d), (2, c), (3, c), (2, b), (3, b), (2, a), (3, a)].

?- cartesian([1,2,3,4,5],[a,b,c,d],Z).
Z = [(1, a), (1, b), (1, c), (1, d), (2, d), (3, d), (4, d), (5, d), (2, c), (3, c), (4, c), (5, c), (2, b), (3, b), (4, b), (5, b), (2, a), (3, a), (4, a), (5, a)].


*/

/* CHECK IF POWERSETS ARE SAME. */

eqbr((X,Y),(P,Q)) :- (((X==P),(Y==Q));((X==Q),(Y==P))),!.


eqss([X],[Y]) :- eqsets(X,Y),!. 

check([],[]) :- !.
check([X],[]) :- fail.
check([[]],[X]) :- !.
check([[]],X) :- !.
check([],X) :- !.
check([],[X]) :- !.
check([X|R1],[Y|R2]) :- (eqsets(X,Y);check([X],R2)),check(R1,[Y|R2]),!.   

% checker([X|R1],PW2) :- check([X|R1],PW2), check(R1,PW2),!.


/*FINAL*/
powerChecker(X,Y) :- check(X,Y),check(Y,X),!.

/*  TEST CASES  */
/*
?- powerChecker([],[]).
true.

?- powerChecker([[a]],[]).
false.

?- powerChecker([],[[a]]).
false.

-- POWERSET OF [1,2,3] AND [3,1,2]
?- powerChecker([[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [2], [3], []],[[3, 1, 2], [3, 1], [3, 2], [3], [1, 2], [1], [2], []]).
true.

--REMOVED [3,2] FROM RIGHT SIDE SET
?- powerChecker([[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [2], [3], []],[[3, 1, 2], [3, 1], [3], [1, 2], [1], [2], []]).
false.

--REMOVED [2] FROM LEFT SIDE
?- powerChecker([[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [3], []],[[3, 1, 2], [3, 1], [3, 2], [3], [1, 2], [1], [2], []]).
false.

--ADDED [a] RIGHT SIDE
?- powerChecker([[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [3], []],[[3, 1, 2], [3, 1], [3, 2], [3], [1, 2], [1], [2], [],[a]]).
false.

--ADDED [a] LEFT SIDE
?- powerChecker([[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [3], [a], []],[[3, 1, 2], [3, 1], [3, 2], [3], [1, 2], [1], [2], []]).
false.


*/
